import SciLean
import SciLean.Util.Profile
import SciLean.Tactic.LetNormalize
import SciLean.Util.RewriteBy

open SciLean

variable 
  {K : Type} [RealScalar K]
  {X : Type} [SemiInnerProductSpace K X]
  {Y : Type} [SemiInnerProductSpace K Y]
  {Z : Type} [SemiInnerProductSpace K Z]
  {W : Type} [SemiInnerProductSpace K W]
  {E : ι → Type _} [∀ i, SemiInnerProductSpace K (E i)]


set_default_scalar K 

theorem revCDeriv.factor_through_app [Index I] [Nonempty I] [Index J]
  (f : I → Y → Z) (g : X → J → Y) (h : I → J)
  (hf : ∀ i, HasAdjDiff K (f i)) (hg : HasAdjDiff K g) 
  (hg' : ∀ j, HasAdjDiff K (g · j)) (hh : Function.Bijective h)
  : (revCDeriv K fun x i => f i ((g x) (h i)))
    = 
    let df' := fun i => gradient K (fun y => f i y)
    let ih := Function.invFun h
    fun x => 
      let jydg := revCDeriv K g x
      (fun i => f i (jydg.1 (h i)), 
       fun dz => 
         let rhs := fun j => df' (ih j) (jydg.1 j) (dz (ih j))
         jydg.2 rhs) := 
by
  conv => 
    lhs
    autodiff
    simp [revCDeriv]
  funext x
  simp[revCDeriv,gradient]
  funext dz
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  sorry_proof -- it should be possible to push the sum inside and be done


theorem revCDeriv.factor_through_getElem 
  {I J JY} [ArrayType JY J Y] [Index I] [Nonempty I] [Index J] 
  (f : I → Y → Z) (g : X → JY) (h : I → J)
  (hf : ∀ i, HasAdjDiff K (f i)) (hg : HasAdjDiff K g) (hg' : ∀ i, HasAdjDiff K (fun x => (g x)[i])) (hh : Function.Bijective h)
  : (revCDeriv K fun x i => f i ((g x)[h i]))
    = 
    let df' := fun i => gradient K (fun y => f i y)
    let ih := Function.invFun h
    fun x => 
      let jydg := revCDeriv K g x
      (fun i => f i (jydg.1[h i]), 
       fun dz => 
         let rhs := introElem (Cont:=JY) (fun j => df' (ih j) (jydg.1[j]) (dz (ih j)))
         jydg.2 rhs) := 
by
  conv => 
    lhs
    autodiff
    simp [revCDeriv]
  funext x
  simp[revCDeriv,gradient]
  funext dz
  set_option trace.Meta.Tactic.simp.discharge true in
  ftrans only
  sorry_proof -- it should be possible to push the sum inside and be done


variable {ι κ : Type} [Index κ] [Index ι] [Nonempty ι] [Nonempty κ] [PlainDataType K]

theorem revCDeriv.pi_uncurry_rule (f : ι → κ → X → Y) (hf : ∀ i j, HasAdjDiff K (f i j))
  : (<∂ x, fun i j => f i j x)
    =
    fun x =>
      let ydf := <∂ x':=x, fun ij : ι×κ => f ij.1 ij.2 x'
      (fun i j => ydf.1 (i,j), 
       fun dy => ydf.2 (fun ij : ι×κ => dy ij.1 ij.2)) := 
by
  sorry

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------


example (x : W → K ^ ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i])) (hx : HasAdjDiff K x)
  : <∂ (fun w i => (x w)[i])
    =
    fun w => 
      let xdx := <∂ (w':=w), x w'
      (fun i => xdx.1[i], fun dy => let dy' := ⊞ i => dy i; xdx.2 dy') :=
by 
  have q := revCDeriv.factor_through_getElem (K:=K) (fun _ y => y) (fun w => x w) (fun i => i) sorry sorry sorry sorry
  rw[q]
  conv => lhs; autodiff


example 
  : <∂ (fun (x : K ^ ι) i => x[i])
    =
    fun x => 
      (fun i => x[i], fun dy => ⊞ i => dy i) :=
by 
  have q := revCDeriv.factor_through_getElem (K:=K) (fun _ y => y) (fun x : K ^ ι => x) (fun i => i) sorry sorry sorry sorry
  rw[q]
  conv => lhs; autodiff


example 
  : <∂ (fun (x : K ^ ι) i => (2:K) * x[i])
    =
    fun x => 
      (fun i => (2:K) * x[i], fun dy => ⊞ i => (2:K) * dy i) :=
by 
  have q := revCDeriv.factor_through_getElem (K:=K) (fun _ y => 2 * y) (fun x : K ^ ι => x) (fun i => i) sorry sorry sorry sorry
  rw[q]
  conv => lhs; autodiff


example 
  (A : ι → κ → K)
  : <∂ (fun (x : K ^ κ) i => ∑ j, A i j * x[j])
    =
    fun x => 
      (fun i => ∑ j, A i j * x[j], 
       fun dy => ⊞ j => ∑ i, A i j * dy i) :=
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y i => A i j * y) (fun x : K ^ κ => x) (fun i => i) sorry sorry sorry sorry]
    autodiff
    autodiff


example 
  (A : ι → κ → K) (x : W → K ^ κ) (hx : HasAdjDiff K x)
  : <∂ (fun w i => ∑ j, A i j * (x w)[j])
    =
    fun w => 
      let xdx := <∂ x w
      (fun i => ∑ j, A i j * xdx.1[j], 
       fun dy => 
         let dx := ⊞ j => ∑ i, A i j * dy i
         xdx.2 dx)
      := 
      -- (fun i => ∑ j, A i j * x[j], 
      --  fun dy => ⊞ j => ∑ i, A i j * dy i) :=
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y i => A i j * y) x (fun i => i) sorry sorry sorry sorry]
    autodiff
    let_normalize
    simp (config := {zeta:=false}) only
    autodiff


example (A : W → (ι×κ) → K) (x : κ → K) (hA : ∀ ij, HasAdjDiff K (A · ij))
  : (<∂ w, fun i => ∑ j, A w (i,j) * x j)
    =
    fun w => 
      let AdA := <∂ A w
      (fun i : ι => ∑ (j : κ), AdA.1 (i,j) * x j,
       fun dy => 
         let dA := fun ij => x ij.2 * dy ij.1
         AdA.2 dA) := 
by 
  conv => 
    lhs
    conv => 
      enter [w,2,w']
      simp only [← sum_lambda_swap]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.pi_uncurry_rule _ sorry]
    simp (config := {zeta:=false}) only 
      [revCDeriv.factor_through_app (K:=K)
        (fun (ji : κ×ι) A => A * x ji.1) A (fun ji => (ji.2, ji.1)) sorry sorry sorry sorry]
    let_normalize
    autodiff
    unfold hold
    let_normalize
    simp (config := {zeta:=false}) only
      [show (Function.invFun fun ji : κ×ι => (ji.snd, ji.fst))
            =
            fun ij : ι×κ => (ij.2, ij.1) by sorry]

example 
  (A : ι → κ → K)
  : (<∂ (x : K ^ κ), ⊞ i => ∑ j, A i j * x[j])
    =
    fun x => 
      (⊞ i => ∑ j, A i j * x[j], 
       fun dy => ⊞ j => ∑ i, A i j * dy[i]) :=
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y => ⊞ i => A i j * y) (fun x : K ^ κ => x) (fun i => i) sorry sorry sorry sorry]
    autodiff
    autodiff

example 
  (A : ι → κ → K) (x : W → K ^ κ) (hx : HasAdjDiff K x)
  : <∂ (fun w => ⊞ i => ∑ j, A i j * (x w)[j])
    =
    fun w => 
      let xdx := <∂ x w
      (⊞ i => ∑ j, A i j * xdx.1[j], 
       fun dy => 
         let dx := ⊞ j => ∑ i, A i j * dy[i]
         xdx.2 dx)
      := 
      -- (fun i => ∑ j, A i j * x[j], 
      --  fun dy => ⊞ j => ∑ i, A i j * dy i) :=
by 
  conv => 
    lhs
    conv => 
      enter [x,2,x]
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y => ⊞ i => A i j * y) x (fun i => i) sorry sorry sorry sorry]
    autodiff
    -- autodiff -- for some reason it is unfolding let binding here :(
    simp (config := {zeta:=false})
    let_normalize
    simp (config := {zeta:=false})


variable (A : DataArrayN K (ι×κ)) (i : ι) (j : κ)

#check A[(i,j)]

#check IntroElem.introElem.arg_f.revCDeriv_rule

example (x : K ^ κ)
  : (<∂ (A : DataArrayN K (ι×κ)), ⊞ i => ∑ j, A[(i,j)] * x[j])
    =
    fun A : K ^ (ι×κ) => 
      (⊞ i : ι => ∑ (j : κ), A[(i,j)] * x[j],
       fun dy => ⊞ ij => dy[ij.1] * x[ij.2]) := 
by 
  conv => 
    lhs
    conv => 
      enter [A,2,A']
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    autodiff
    simp (config := {zeta:=false}) only [IntroElem.introElem.arg_f.revCDeriv_rule _ sorry]

    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y => ⊞ i => A i j * y) (fun x : K ^ κ => x) (fun i => i) sorry sorry sorry sorry]
    autodiff
    autodiff



example (A : W → DataArrayN K (ι×κ)) (x : K ^ κ) (hA : HasAdjDiff K A)
  : (<∂ w, ⊞ i => ∑ j, (A w)[(i,j)] * x[j])
    =
    fun w => 
      let AdA := <∂ A w
      (⊞ i : ι => ∑ (j : κ), AdA.1[(i,j)] * x[j],
       fun dy => 
         let dA := ⊞ ij => dy[ij.1] * x[ij.2]
         AdA.2 dA) := 
by 
  conv => 
    lhs
    conv => 
      enter [w,2,w']
      simp only [← ArrayType.sum_introElem]
    simp (config := {zeta:=false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
    autodiff
    simp (config := {zeta:=false}) only [IntroElem.introElem.arg_f.revCDeriv_rule _ sorry]

    simp (config := {zeta:=false}) only [revCDeriv.factor_through_getElem (K:=K) (fun j y => ⊞ i => A i j * y) (fun x : K ^ κ => x) (fun i => i) sorry sorry sorry sorry]
    autodiff
    autodiff


  




example [Index ι] [PlainDataType K] (x : W → K ^ ι) (hx : ∀ i, HasAdjDiff K (fun w => (x w)[i]))
  : <∂ w, ∑ i, (x w)[i]
    =
    fun w =>
      let xdx := <∂ (w':=w), x w'
      (∑ i, xdx.1[i], fun dy' => xdx.2 (⊞ _ => dy')) := 
by
  set_option trace.Meta.Tactic.simp.rewrite true in
  conv => 
    lhs
    simp (config := {zeta := false}) only [EnumType.sum.arg_f.revCDeriv_rule _ sorry]
  


  


