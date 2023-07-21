import Qq
import Lean.Meta.Tactic.Simp.Types

import Std.Data.RBMap.Alter

import Mathlib.Data.FunLike.Basic

import SciLean.Prelude
import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
 
open Lean Meta.Simp Qq

namespace SciLean.FTrans


-- Tracing --
-------------
initialize registerTraceClass `Meta.Tactic.ftrans
initialize registerTraceClass `Meta.Tactic.ftrans.step
initialize registerTraceClass `Meta.Tactic.ftrans.missing_rule
-- initialize registerTraceClass `Meta.Tactic.ftrans.normalize_let
initialize registerTraceClass `Meta.Tactic.ftrans.rewrite
initialize registerTraceClass `Meta.Tactic.ftrans.discharge
initialize registerTraceClass `Meta.Tactic.ftrans.unify
-- initialize registerTraceClass `Meta.Tactic.ftrans.lambda_special_cases


/-- Simp attribute to mark function transformation rules.
-/
register_simp_attr ftrans_simp

macro "ftrans" : attr => `(attr| ftrans_simp ↓)


open Meta Simp


-- TODO: Move RewriteRule to a new file and add a custom version `tryTheorem?` with proper tracing

/-- Rewrite rule can be either provided as a theorem or as a meta program
-/
inductive RewriteRule where
  | thm  (name : Name) 
  | eval (f : Expr → MetaM (Option Result))
deriving Inhabited


def RewriteRule.apply (r : RewriteRule) (discharger : Expr → SimpM (Option Expr)) (e : Expr) : SimpM (Option Result) := 
  match r with
  | eval f => f e
  | thm name => do

    let thm : SimpTheorem := {
      proof := mkConst name
      origin := .decl name
      rfl := false
    }

    let .some result ← Meta.Simp.tryTheorem? e thm discharger
      | return none
    return result


structure FTransExt where
  /-- Function transformation name -/
  ftransName : Name
  /-- Get function being transformed from function transformation expression -/
  getFTransFun?    (expr : Expr) : Option Expr
  /-- Replace function being transformed in function transformation expression -/
  replaceFTransFun (expr : Expr) (newFun : Expr) : Expr
  /-- Custom rule for transforming `fun x => x -/
  identityRule     : Option RewriteRule
  /-- Custom rule for transforming `fun x => y -/
  constantRule    : Option RewriteRule
  /-- Custom rule for transforming `fun x => let y := g x; f x y -/
  lambdaLetRule    : Option RewriteRule
  /-- Custom rule for transforming `fun x y => f x y -/
  lambdaLambdaRule : Option RewriteRule
  /-- Custom discharger for this function transformation -/
  discharger       : Expr → SimpM (Option Expr)
  /-- Name of this extension, keep the default value! -/
  name : Name := by exact decl_name%
deriving Inhabited


def FTransExt.applyLambdaLetRule (ext : FTransExt) (e : Expr) : SimpM Step := do
  let .some r := ext.lambdaLetRule 
    | trace[Meta.Tactic.ftrans.missing_rule] "Missing lambda-let rule a rule for `{ext.ftransName}`"
      return .visit { expr := e }

  if let .some r ← r.apply (ext.discharger ·) e then
    return .visit r
  else
    trace[Meta.Tactic.ftrans.discharge] "Failed applying lambda-let rule to `{← ppExpr e}"
    return .visit { expr := e }

def FTransExt.applyLambdaLambdaRule (ext : FTransExt) (e : Expr) : SimpM Step := do
  let .some r := ext.lambdaLambdaRule 
    | trace[Meta.Tactic.ftrans.missing_rule] "Missing lambda-lambda rule a rule for `{ext.ftransName}`"
      return .visit { expr := e }

  if let .some r ← r.apply (ext.discharger ·) e then
    return .visit r
  else
    trace[Meta.Tactic.ftrans.discharge] "Failed applying lambda-lambda rule to `{← ppExpr e}"
    return .visit { expr := e }

def FTransExt.applyIdentityRule (ext : FTransExt) (e : Expr) : SimpM Step := do
  let .some r := ext.identityRule 
    | trace[Meta.Tactic.ftrans.missing_rule] "Missing identity rule a rule for `{ext.ftransName}`"
      return .visit { expr := e }

  if let .some r ← r.apply (ext.discharger ·) e then
    return .visit r
  else
    trace[Meta.Tactic.ftrans.discharge] "Failed applying identity rule to `{← ppExpr e}"
    return .visit { expr := e }

def FTransExt.applyConstantRule (ext : FTransExt) (e : Expr) : SimpM Step := do
  let .some r := ext.constantRule 
    | trace[Meta.Tactic.ftrans.missing_rule] "Missing constant rule a rule for `{ext.ftransName}`"
      return .visit { expr := e }

  if let .some r ← r.apply (ext.discharger ·) e then
    return .visit r
  else
    trace[Meta.Tactic.ftrans.discharge] "Failed applying constant rule to `{← ppExpr e}"
    return .visit { expr := e }


def mkFTransExt (n : Name) : ImportM FTransExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck FTransExt opts ``FTransExt n


initialize ftransExt : PersistentEnvExtension (Name × Name) (Name × FTransExt) (Std.RBMap Name FTransExt Name.quickCmp) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun s => do

      let mut r : Std.RBMap Name FTransExt Name.quickCmp := {}

      for s' in s do
        for (ftransName, extName) in s' do
          let ext ← mkFTransExt extName
          r := r.insert ftransName ext

      pure r
    addEntryFn := fun s (n, ext) => s.insert n ext
    exportEntriesFn := fun s => s.valuesArray.map (fun ext => (ext.ftransName, ext.name))
  }

/-- 
  Returns function transformation name and function being tranformed if `e` is function tranformation expression.
 -/
def getFTrans? (e : Expr) : CoreM (Option (Name × FTransExt × Expr)) := do

  let .some ftransName := 
      match e.getAppFn.constName? with
      | none => none
      | .some name => 
        if name != ``FunLike.coe then
          name
        else if let .some ftrans := e.getArg? 4 then
          ftrans.getAppFn.constName? 
        else
          none
    | return none

  let .some ext := (ftransExt.getState (← getEnv)).find? ftransName
    | return none

  let .some f := ext.getFTransFun? e
    | return none

  return (ftransName, ext, f)

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFTransExt? (e : Expr) : CoreM (Option FTransExt) := do
  let .some (_, ext, _) ← getFTrans? e
    | return none
  return ext

/-- 
  Returns function transformation info if `e` is function btranformation expression.
 -/
def getFTransFun? (e : Expr) : CoreM (Option Expr) := do
  let .some (_, _, f) ← getFTrans? e
    | return none
  return f


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

initialize registerTraceClass `trace.Tactic.ftrans.new_property

local instance : Ord Name := ⟨Name.quickCmp⟩
/-- 
This holds a collection of property theorems for a fixed constant
-/
def FTransRules := Std.RBMap Name (Std.RBSet Name compare /- maybe (Std.RBSet SimTheorem ...) -/) compare

namespace FTransRules

  instance : Inhabited FTransRules := by unfold FTransRules; infer_instance
  instance : ToString FTransRules := ⟨fun s => toString (s.toList.map fun (n,r) => (n,r.toList))⟩

  variable (fp : FTransRules)

  def insert (property : Name) (thrm : Name) : FTransRules := 
    fp.alter property (λ p? =>
      match p? with
      | some p => some (p.insert thrm)
      | none => some (Std.RBSet.empty.insert thrm))

  def empty : FTransRules := Std.RBMap.empty

end FTransRules

private def FTransRules.merge! (function : Name) (fp fp' : FTransRules) :  FTransRules :=
  fp.mergeWith (t₂ := fp') λ _ p q => p.union q

initialize FTransRulesExt : MergeMapDeclarationExtension FTransRules 
  ← mkMergeMapDeclarationExtension ⟨FTransRules.merge!, sorry_proof⟩

open Lean Qq Meta Elab Term in
initialize funTransRuleAttr : TagAttribute ← 
  registerTagAttribute 
    `ftrans_rule
    "Attribute to tag the basic rules for a function transformation." 
    (validate := fun ruleName => do
      let env ← getEnv 
      let .some ruleInfo := env.find? ruleName 
        | throwError s!"Can't find a constant named `{ruleName}`!"

      let rule := ruleInfo.type

      MetaM.run' do
        forallTelescope rule λ _ eq => do

          let .some (_,lhs,_) := eq.app3? ``Eq
            | throwError s!"`{← ppExpr eq}` is not a rewrite rule!"

          let .some (transName, _, f) ← getFTrans? lhs
            | throwError s!
"`{← ppExpr eq}` is not a rewrite rule of known function transformaion!
To register function transformation call:
```
#eval show Lean.CoreM Unit from do
  FTrans.FTransExt.insert <name> <info>
```
where <name> is name of the function transformation and <info> is corresponding `FTrans.Info`. 
"
          let .some funName ← getFunHeadConst? f
            | throwError "Function being transformed is in invalid form!"

          FTransRulesExt.insert funName (FTransRules.empty.insert transName ruleName)
      )           

open Meta in
def getFTransRules (funName ftransName : Name) : CoreM (Array SimpTheorem) := do

  let .some rules ← FTransRulesExt.find? funName
    | return #[]

  let .some rules := rules.find? ftransName
    | return #[]

  let rules : List SimpTheorem ← rules.toList.mapM fun r => do
    return { 
      proof  := mkConst r
      origin := .decl r
      rfl    := false
    }

  return rules.toArray

  
