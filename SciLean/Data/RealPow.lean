import SciLean.Mathlib.Data.PowType
import SciLean.Categories
import SciLean.Data.Table

namespace SciLean

instance (n : Nat) : PowType ℝ n := 
{
  powType := {a : FloatArray // a.size = n}
  intro := λ f => Id.run do
    let mut x := FloatArray.mkEmpty n
    for i in [0:n] do
      let i := ⟨i, sorry⟩
      x := x.push (f i)
    ⟨x, sorry⟩
  get := λ x i => x.1.get ⟨i.1, sorry⟩
  set := λ x i xi => ⟨x.1.set ⟨i.1, sorry⟩ xi, sorry⟩
  ext := sorry
}


-- following should be generalized for any table but I'm having some issues with TC

instance (n : Nat) : AddSemigroup (ℝ^n) := AddSemigroup.mk sorry
instance (n : Nat) : AddMonoid (ℝ^n)    := AddMonoid.mk sorry sorry nsmul_rec sorry sorry
instance (n : Nat) : AddCommMonoid (ℝ^n) := AddCommMonoid.mk sorry
instance (n : Nat) : SubNegMonoid (ℝ^n) := SubNegMonoid.mk sorry gsmul_rec sorry sorry sorry
instance (n : Nat) : AddGroup (ℝ^n)     := AddGroup.mk sorry
instance (n : Nat) : AddCommGroup (ℝ^n) := AddCommGroup.mk sorry

set_option synthInstance.maxHeartbeats 3000 in
instance (n : Nat) : MulAction ℝ (ℝ^n) := MulAction.mk sorry sorry
instance (n : Nat) : DistribMulAction ℝ (ℝ^n) := DistribMulAction.mk sorry sorry
instance (n : Nat) : Module ℝ (ℝ^n) := Module.mk sorry sorry

instance (n : Nat)  : Vec (ℝ^n) := Vec.mk

instance (n : Nat) : SemiInner (ℝ^n) ℝ Unit (λ r _ => r) :=
{
  semiInner := λ x y => ∑ i, x[i] * y[i]
  testFunction := λ _ _ => True
}

instance (n : Nat) : Hilbert (ℝ^n) :=
{
  semi_inner_add := sorry
  semi_inner_mul := sorry
  semi_inner_sym := sorry
  semi_inner_pos := sorry
  semi_inner_ext := sorry
}

instance (n : Nat) (i : Fin n)  : IsLin (λ c : ℝ^n => c[i]) := sorry
instance (n : Nat) : IsLin (λ (c : (ℝ^n)) (i : Fin n)  => c[i]) := sorry

instance (n : Nat) 
  : HasAdjoint (λ (c : ℝ^n) (i : Fin n) => c[i]) := sorry
instance (n : Nat) (i : Fin n)
  : HasAdjoint (λ c : ℝ^n => c[i]) := sorry


-- @[simp]
-- theorem adjoint_of_pullback {ι κ} [Enumtype ι] [Enumtype κ] [Nonempty ι] 
--   (g : ι → κ) [IsInv g]
--   : 
--     adjoint (λ (f : κ → X) i => f (g i)) = (λ f => f ∘ g⁻¹) 
--   := 
-- by 
--   admit


@[simp]                         
theorem adjoint_of_Rn_get (n : Nat)
  : (λ (u : ℝ^n) i => u[i])† = Table.intro :=
by 
  funext x;
  inner_ext;
  simp (discharger := assumption)
  simp[SemiInner.semiInner',SemiInner.semiInner]
  done

def u : (ℝ^(2 : Nat)) := ^[-2.0,2.0]

#eval u[(1 : Fin 2)]
#eval (u + u : ℝ^(2 : Nat))
#eval 2*⟪u, u⟫

open Table Trait
example : Table.Trait (ℝ^(2 : Nat)) := by infer_instance
example : Table (ℝ^(2 : Nat)) (Index (ℝ^(2 : Nat))) (Value (ℝ^(2 : Nat))) := by infer_instance
example : Enumtype (Index (ℝ^(2 : Nat))) := by infer_instance
example : SemiInner (Value (ℝ^(2 : Nat))) ℝ Unit (λ r _ => r) := by infer_instance
example : SemiInner (ℝ^(2 : Nat)) ℝ Unit (λ r _ => r) := by infer_instance
example : SemiInner.Trait (ℝ^(2 : Nat)) := by infer_instance
