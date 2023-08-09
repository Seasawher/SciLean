import SciLean.Core.FunctionPropositions.HasAdjDiffAt
import SciLean.Core.FunctionPropositions.HasAdjDiff

import SciLean.Core.FunctionTransformations.SemiAdjoint
  
import SciLean.Profile

set_option linter.unusedVariables false

namespace SciLean

noncomputable
def revCDeriv
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  (f : X → Y) (x : X) : Y×(Y→X) :=
  (f x, semiAdjoint K (cderiv K f x))


namespace revCDeriv

variable 
  (K : Type _) [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

-- this one is dangerous as it can be applied to rhs again with g = fun x => x
-- we need ftrans guard or something like that
theorem _root_.SciLean.cderiv.arg_dx.semiAdjoint_rule
  (f : Y → Z) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun dx => cderiv K f y (g dx))
    =
    fun dz => 
      semiAdjoint K g (semiAdjoint K (cderiv K f y) dz) := 
by
  apply semiAdjoint.comp_rule K (cderiv K f y) g (hf.2 y) hg

theorem _root_.SciLean.cderiv.arg_dx.semiAdjoint_rule_at
  (f : Y → Z) (g : X → Y) (y : Y)
  (hf : HasAdjDiffAt K f y) (hg : HasSemiAdjoint K g)
  : semiAdjoint K (fun dx => cderiv K f y (g dx))
    =
    fun dz => 
      semiAdjoint K g (semiAdjoint K (cderiv K f y) dz) := 
by
  apply semiAdjoint.comp_rule K (cderiv K f y) g hf.2 hg


-- Basic lambda calculus rules -------------------------------------------------
--------------------------------------------------------------------------------

variable (X)
theorem id_rule 
  : revCDeriv K (fun x : X => x) = fun x => (x, fun dx => dx) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans


theorem const_rule (y : Y)
  : revCDeriv K (fun _ : X => y) = fun x => (y, fun _ => 0) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans
variable{X}

variable(E)
theorem proj_rule [DecidableEq ι] (i : ι)
  : revCDeriv K (fun (x : (i:ι) → E i) => x i)
    = 
    fun x => 
      (x i, fun dxi j => if h : i=j then h ▸ dxi else 0) :=
by
  unfold revCDeriv
  funext _; ftrans; ftrans
variable {E}


theorem comp_rule 
  (f : Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : revCDeriv K (fun x : X => f (g x))
    = 
    fun x =>
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K f ydg.1
      (zdf.1,
       fun dz =>
         let dy := zdf.2 dz
         ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; ftrans; ftrans


theorem let_rule 
  (f : X → Y → Z) (g : X → Y) 
  (hf : HasAdjDiff K (fun (xy : X×Y) => f xy.1 xy.2)) (hg : HasAdjDiff K g)
  : revCDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; ftrans; ftrans 


open BigOperators in
theorem pi_rule
  (f : (i : ι) → X → E i) (hf : ∀ i, HasAdjDiff K (f i))
  : (revCDeriv K fun (x : X) (i : ι) => f i x)
    =
    fun x =>
      let xdf := fun i =>
        (revCDeriv K fun (x : X) => f i x) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revCDeriv
  funext _; ftrans; ftrans 


theorem comp_rule_at
  (f : Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K f (g x)) (hg : HasAdjDiffAt K g x)
  : revCDeriv K (fun x : X => f (g x)) x
    = 
    let ydg := revCDeriv K g x
    let zdf := revCDeriv K f ydg.1
    (zdf.1,
     fun dz =>
       let dy := zdf.2 dz
       ydg.2 dy)  := 
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; ftrans; simp
  rw[cderiv.arg_dx.semiAdjoint_rule_at K f (cderiv K g x) (g x) (by fprop) (by fprop)]


theorem let_rule_at
  (f : X → Y → Z) (g : X → Y) (x : X)
  (hf : HasAdjDiffAt K (fun (xy : X×Y) => f xy.1 xy.2) (x, g x)) (hg : HasAdjDiffAt K g x)
  : revCDeriv K (fun x : X => let y := g x; f x y) 
    = 
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K (fun (xy : X×Y) => f xy.1 xy.2) (x,ydg.1)
      (zdf.1,
       fun dz => 
         let dxdy := zdf.2 dz
         let dx := ydg.2 dxdy.2
         dxdy.1 + dx)  :=
by
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv
  funext _; simp; sorry


open BigOperators in
theorem pi_rule_at
  (f : (i : ι) → X → E i) (x : X) (hf : ∀ i, HasAdjDiffAt K (f i) x)
  : (revCDeriv K fun (x : X) (i : ι) => f i x)
    =
    fun x =>
      let xdf := fun i =>
        (revCDeriv K fun (x : X) => f i x) x
      (fun i => (xdf i).1,
       fun dy => ∑ i, (xdf i).2 (dy i))
       :=
by
  have _ := fun i => (hf i).1
  have _ := fun i => (hf i).2
  unfold revCDeriv
  funext _; ftrans; ftrans 
  sorry


-- Register `revCDeriv` as function transformation ------------------------------
--------------------------------------------------------------------------------

open Lean Meta Qq in
def discharger (e : Expr) : SimpM (Option Expr) := do
  withTraceNode `revCDeriv_discharger (fun _ => return s!"discharge {← ppExpr e}") do
  let cache := (← get).cache
  let config : FProp.Config := {}
  let state  : FProp.State := { cache := cache }
  let (proof?, state) ← FProp.fprop e |>.run config |>.run state
  modify (fun simpState => { simpState with cache := state.cache })
  if proof?.isSome then
    return proof?
  else
    -- if `fprop` fails try assumption
    let tac := FTrans.tacticToDischarge (Syntax.mkLit ``Lean.Parser.Tactic.assumption "assumption")
    let proof? ← tac e
    return proof?


open Lean Meta FTrans in
def ftransExt : FTransExt where
  ftransName := ``revCDeriv

  getFTransFun? e := 
    if e.isAppOf ``revCDeriv then

      if let .some f := e.getArg? 6 then
        some f
      else 
        none
    else
      none

  replaceFTransFun e f := 
    if e.isAppOf ``revCDeriv then
      e.modifyArg (fun _ => f) 6
    else          
      e

  idRule  e X := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``id_rule #[K, X], origin := .decl ``id_rule, rfl := false} ]
      discharger e

  constRule e X y := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``const_rule #[K, X, y], origin := .decl ``const_rule, rfl := false} ]
      discharger e

  projRule e X i := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``proj_rule #[K, X, i], origin := .decl ``proj_rule, rfl := false} ]
      discharger e

  compRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``comp_rule #[K, f, g], origin := .decl ``comp_rule, rfl := false},
         { proof := ← mkAppM ``comp_rule_at #[K, f, g], origin := .decl ``comp_rule, rfl := false} ]
      discharger e

  letRule e f g := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``let_rule #[K, f, g], origin := .decl ``let_rule, rfl := false},
         { proof := ← mkAppM ``let_rule_at #[K, f, g], origin := .decl ``let_rule, rfl := false} ]
      discharger e

  piRule  e f := do
    let .some K := e.getArg? 0 | return none
    tryTheorems
      #[ { proof := ← mkAppM ``pi_rule #[K, f], origin := .decl ``pi_rule, rfl := false},
         { proof := ← mkAppM ``pi_rule_at #[K, f], origin := .decl ``pi_rule, rfl := false} ]
      discharger e

  discharger := discharger


-- register revCDeriv
open Lean in
#eval show CoreM Unit from do
  modifyEnv (λ env => FTrans.ftransExt.addEntry env (``revCDeriv, ftransExt))


end SciLean.revCDeriv

--------------------------------------------------------------------------------
-- Function Rules --------------------------------------------------------------
--------------------------------------------------------------------------------b

open SciLean

variable 
  {K : Type _} [IsROrC K]
  {X : Type _} [SemiInnerProductSpace K X]
  {Y : Type _} [SemiInnerProductSpace K Y]
  {Z : Type _} [SemiInnerProductSpace K Z]
  {ι : Type _} [Fintype ι]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


-- Prod.mk -----------------------------------v---------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.mk.arg_fstsnd.revCDeriv_rule_at
  (g : X → Y) (f : X → Z) (x : X)
  (hg : HasAdjDiffAt K g x) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (g x, f x)) x
    =
    let ydg := revCDeriv K g x
    let zdf := revCDeriv K f x
    ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem Prod.mk.arg_fstsnd.revCDeriv_rule
  (g : X → Y) (f : X → Z)
  (hg : HasAdjDiff K g) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (g x, f x))
    =
    fun x => 
      let ydg := revCDeriv K g x
      let zdf := revCDeriv K f x
      ((ydg.1,zdf.1), fun dyz => ydg.2 dyz.1 + zdf.2 dyz.2) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp
 

-- Prod.fst --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.fst.arg_self.revCDeriv_rule_at
  (f : X → Y×Z) (x : X) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (f x).1) x
    =
    let yzdf := revCDeriv K f x
    (yzdf.1.1, fun dy => yzdf.2 (dy,0)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp

@[ftrans]
theorem Prod.fst.arg_self.revCDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (f x).1)
    =
    fun x => 
      let yzdf := revCDeriv K f x
      (yzdf.1.1, fun dy => yzdf.2 (dy,0)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp


-- ProdL2.snd --------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Prod.snd.arg_self.revCDeriv_rule_at
  (f : X → Y×Z) (x : X) (hf : HasAdjDiffAt K f x)
  : revCDeriv K (fun x => (f x).2) x
    =
    let yzdf := revCDeriv K f x
    (yzdf.1.2, fun dz => yzdf.2 (0,dz)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem Prod.snd.arg_self.revCDeriv_rule
  (f : X → Y×Z) (hf : HasAdjDiff K f)
  : revCDeriv K (fun x => (f x).2)
    =
    fun x => 
      let yzdf := revCDeriv K f x
      (yzdf.1.2, fun dz => yzdf.2 (0,dz)) := 
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; ftrans; ftrans; simp


-- HAdd.hAdd -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revCDeriv_rule_at
  (f g : X → Y) (x : X) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x + g x) x
    =
    let ydf := revCDeriv K f x
    let ydg := revCDeriv K g x
    (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HAdd.hAdd.arg_a0a1.revCDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x + g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let ydg := revCDeriv K g x
      (ydf.1 + ydg.1, fun dy => ydf.2 dy + ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HSub.hSub -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSub.hSub.arg_a0a1.revCDeriv_rule_at
  (f g : X → Y) (x : X) (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x - g x) x
    =
    let ydf := revCDeriv K f x
    let ydg := revCDeriv K g x
    (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HSub.hSub.arg_a0a1.revCDeriv_rule
  (f g : X → Y) (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x - g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let ydg := revCDeriv K g x
      (ydf.1 - ydg.1, fun dy => ydf.2 dy - ydg.2 dy) := 
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- Neg.neg ---------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem Neg.neg.arg_a0.revCDeriv_rule
  (f : X → Y) (x : X) 
  : (revCDeriv K fun x => - f x) x
    =
    let ydf := revCDeriv K f x
    (-ydf.1, fun dy => - ydf.2 dy) :=
by 
  unfold revCDeriv; simp; ftrans; ftrans


-- HMul.hmul -------------------------------------------------------------------
--------------------------------------------------------------------------------
open ComplexConjugate

@[ftrans]
theorem HMul.hMul.arg_a0a1.revCDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x * g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 * zdg.1, fun dx' =>  conj ydf.1 • zdg.2 dx' + conj zdg.1 • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp

@[ftrans]
theorem HMul.hMul.arg_a0a1.revCDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x * g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 * zdg.1, fun dx' => conj ydf.1 • zdg.2 dx' + conj zdg.1 • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- SMul.smul -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revCDeriv_rule_at
  (f : X → K) (g : X → Y) (x : X) 
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x)
  : (revCDeriv K fun x => f x • g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 • zdg.1, fun dx' => ydf.2 (inner dx' zdg.1) + ydf.1 • zdg.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp; sorry


example 
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → K) (g : X → Y) (x : X)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  (hf' : HasSemiAdjoint K f)
  -- : HasSemiAdjoint K fun x_1 => SciLean.cderiv K f x x_1 • g x
  : HasSemiAdjoint K fun dx : X => f dx • g x
  := by fprop

@[ftrans]
theorem HSMul.hSMul.arg_a0a1.revCDeriv_rule
  {Y : Type _} [NormedAddCommGroup Y] [InnerProductSpace K Y] [CompleteSpace Y]
  (f : X → K) (g : X → Y)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g)
  : (revCDeriv K fun x => f x • g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 • zdg.1, fun dx' => conj ydf.1 • zdg.2 dx' + ydf.2 (inner zdg.1 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HDiv.hDiv -------------------------------------------------------------------
--------------------------------------------------------------------------------

@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revCDeriv_rule_at
  (f g : X → K) (x : X)
  (hf : HasAdjDiffAt K f x) (hg : HasAdjDiffAt K g x) (hx : g x ≠ 0)
  : (revCDeriv K fun x => f x / g x) x
    =
    let ydf := revCDeriv K f x
    let zdg := revCDeriv K g x
    (ydf.1 / zdg.1, 
     fun dx' => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


@[ftrans]
theorem HDiv.hDiv.arg_a0a1.revCDeriv_rule
  (f g : X → K)
  (hf : HasAdjDiff K f) (hg : HasAdjDiff K g) (hx : ∀ x, g x ≠ 0)
  : (revCDeriv K fun x => f x / g x)
    =
    fun x => 
      let ydf := revCDeriv K f x
      let zdg := revCDeriv K g x
      (ydf.1 / zdg.1, 
       fun dx' => (1 / (conj zdg.1)^2) • (conj zdg.1 • ydf.2 dx' - conj ydf.1 • zdg.2 dx')) :=
by 
  have ⟨_,_⟩ := hf
  have ⟨_,_⟩ := hg
  unfold revCDeriv; simp; ftrans; ftrans; simp


-- HPow.hPow -------------------------------------------------------------------
-------------------------------------------------------------------------------- 

@[ftrans]
def HPow.hPow.arg_a0.revCDeriv_rule_at
  (f : X → K) (x : X) (n : Nat) (hf : HasAdjDiffAt K f x) 
  : revCDeriv K (fun x => f x ^ n) x
    =
    let ydf := revCDeriv K f x
    (ydf.1 ^ n, fun dx' => (n * conj ydf.1 ^ (n-1)) • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; simp; ftrans; ftrans; sorry_proof 
  -- just missing (a * b) • x = b • a • x

@[ftrans]
def HPow.hPow.arg_a0.revCDeriv_rule
  (f : X → K) (n : Nat) (hf : HasAdjDiff K f) 
  : revCDeriv K (fun x => f x ^ n)
    =
    fun x => 
      let ydf := revCDeriv K f x
      (ydf.1 ^ n, fun dx' => (n * (conj ydf.1 ^ (n-1))) • ydf.2 dx') :=
by 
  have ⟨_,_⟩ := hf
  unfold revCDeriv; simp; ftrans; ftrans; simp; sorry_proof 
  -- just missing (a * b) • x = b • a • x

