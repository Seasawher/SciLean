import Qq
import Lean.Meta.Tactic.Simp.Types

import Std.Data.RBMap.Alter

import Mathlib.Data.FunLike.Basic

import SciLean.Prelude
import SciLean.Lean.MergeMapDeclarationExtension
import SciLean.Lean.Meta.Basic
 
open Lean Meta.Simp Qq

namespace SciLean.FProp


-- Tracing --
-------------
initialize registerTraceClass `Meta.Tactic.fprop
initialize registerTraceClass `Meta.Tactic.fprop.step
initialize registerTraceClass `Meta.Tactic.fprop.missing_rule
-- initialize registerTraceClass `Meta.Tactic.fprop.normalize_let
initialize registerTraceClass `Meta.Tactic.fprop.rewrite
initialize registerTraceClass `Meta.Tactic.fprop.discharge
initialize registerTraceClass `Meta.Tactic.fprop.unify
initialize registerTraceClass `Meta.Tactic.fprop.apply
-- initialize registerTraceClass `Meta.Tactic.fprop.lambda_special_cases


open Meta 


structure Config where
  -- config

abbrev Cache := ExprMap Expr

structure State where
  cache        : Cache := {}

abbrev _root_.SciLean.FPropM := ReaderT FProp.Config $ StateRefT FProp.State MetaM


structure _root_.SciLean.FPropExt where
  /-- Function transformation name -/
  fpropName : Name
  /-- Get the function  -/
  getFPropFun?    (expr : Expr) : Option Expr
  /-- Replace the function -/
  replaceFTransFun (expr : Expr) (newFun : Expr) : Expr
  /-- Custom rule for proving property of `fun x => x -/
  identityRule     (expr : Expr) : FPropM (Option Expr)
  /-- Custom rule for proving property of `fun x => y -/
  constantRule     (expr : Expr) : FPropM (Option Expr)
  /-- Custom rule for proving property of `fun x => let y := g x; f x y -/
  lambdaLetRule    (expr : Expr) : FPropM (Option Expr)
  /-- Custom rule for proving property of `fun x y => f x y -/
  lambdaLambdaRule (expr : Expr) : FPropM (Option Expr)
  /-- Custom discharger for this function property - like proving (x≠0) -/
  discharger       : Expr → FPropM (Option Expr)
  /-- Name of this extension, keep the default value! -/
  name : Name := by exact decl_name%
deriving Inhabited



def mkFPropExt (n : Name) : ImportM FpropExt := do
  let { env, opts, .. } ← read
  IO.ofExcept <| unsafe env.evalConstCheck FpropExt opts ``FPropExt n


initialize fpropExt : PersistentEnvExtension (Name × Name) (Name × FPropExt) (Std.RBMap Name FPropExt Name.quickCmp) ←
  registerPersistentEnvExtension {
    mkInitial := pure {}
    addImportedFn := fun s => do

      let mut r : Std.RBMap Name FPropExt Name.quickCmp := {}

      for s' in s do
        for (fpropName, extName) in s' do
          let ext ← mkFPropExt extName
          r := r.insert fpropName ext

      pure r
    addEntryFn := fun s (n, ext) => s.insert n ext
    exportEntriesFn := fun s => s.valuesArray.map (fun ext => (ext.fpropName, ext.name))
  }

def getFPropName? (e : Expr) : Option Name := e.getAppFn.constName?

/-- 
  Returns function property name, its extension and the function if `e` is function property expression.
 -/
def getFProp? (e : Expr) : CoreM (Option (Name × FPropExt × Expr)) := do

  let .some fpropName := e.getAppFn.constName?
    | return none

  let .some ext := (fpropExt.getState (← getEnv)).find? fpropName
    | return none

  let .some f := ext.getFPropFun? e
    | return none

  return (fpropName, ext, f)

/-- 
  Returns function transformation info if `e` is function tranformation expression.
 -/
def getFPropExt? (e : Expr) : CoreM (Option FPropExt) := do
  let .some (_, ext, _) ← getFProp? e
    | return none
  return ext

/-- 
  Returns function transformation info if `e` is function btranformation expression.
 -/
def getFPropFun? (e : Expr) : CoreM (Option Expr) := do
  let .some (_, _, f) ← getFProp? e
    | return none
  return f


--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

-- initialize registerTraceClass `trace.Tactic.fprop.new_property

local instance : Ord Name := ⟨Name.quickCmp⟩
/-- 
This holds a collection of property theorems for a fixed constant
-/
def FPropRules := Std.RBMap Name (Std.RBSet Name compare /- maybe (Std.RBSet SimTheorem ...) -/) compare

namespace FPropRules

  instance : Inhabited FPropRules := by unfold FPropRules; infer_instance
  instance : ToString FPropRules := ⟨fun s => toString (s.toList.map fun (n,r) => (n,r.toList))⟩

  def insert (fp : FPropRules) (property : Name) (thrm : Name) : FPropRules := 
    fp.alter property (λ p? =>
      match p? with
      | some p => some (p.insert thrm)
      | none => some (Std.RBSet.empty.insert thrm))

  def empty : FPropRules := Std.RBMap.empty

end FPropRules

private def FPropRules.merge! (function : Name) (fp fp' : FPropRules) :  FPropRules :=
  fp.mergeWith (t₂ := fp') λ _ p q => p.union q

initialize FPropRulesExt : MergeMapDeclarationExtension FPropRules 
  ← mkMergeMapDeclarationExtension ⟨FPropRules.merge!, sorry_proof⟩

open Lean Qq Meta Elab Term in
initialize funTransRuleAttr : TagAttribute ← 
  registerTagAttribute 
    `fprop_rule
    "Attribute to tag the basic rules for a function property." 
    (validate := fun ruleName => do
      let env ← getEnv 
      let .some ruleInfo := env.find? ruleName 
        | throwError s!"Can't find a constant named `{ruleName}`!"

      let rule := ruleInfo.type

      MetaM.run' do
        forallTelescope rule λ _ b => do

          let .some (transName, _, f) ← getFProp? b
            | throwError s!
"`{← ppExpr b}` is not a statement about known function property
To register function transformation call:
```
#eval show Lean.CoreM Unit from do
  FProp.FPropExt.insert <name> <info>
```
where <name> is name of the function transformation and <ext> is corresponding `FPropExp`. 
"
          let .some funName ← getFunHeadConst? f
            | throwError "Function being transformed is in invalid form!"

          FPropRulesExt.insert funName (FPropRules.empty.insert transName ruleName)
      )           

open Meta in
def getFPropRules (funName fpropName : Name) : CoreM (Array SimpTheorem) := do

  let .some rules ← FPropRulesExt.find? funName
    | return #[]

  let .some rules := rules.find? fpropName
    | return #[]

  let rules : List SimpTheorem ← rules.toList.mapM fun r => do
    pure { 
      proof  := mkConst r
      origin := .decl r
      rfl    := false
    }

  return rules.toArray


  