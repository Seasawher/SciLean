import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Scalar.Notation

open SciLean Scalar

-- 係数が実数であると宣言する
set_default_scalar ℝ

/- ## Exercise 4

Let `L(t, x)` be a function of time and space and `y(t)` a function of time.
Express `d/dt L(t, y(t))` and `∂/∂t L(t, y(t))` in Lean.
What is the difference between these two expressions?
-/
section

variable {L : ℝ → ℝ → ℝ} {t : ℝ} {x y : ℝ → ℝ}

#check ∂ (fun t => L t (y t))
#check ∂ (t : ℝ), (L t (y t))

#check (fderiv ℝ (fun (t : ℝ) => L t (y t)))

variable {t₀ : ℝ}

-- `X →L[ℝ] → Y` は線形写像を表しているが、導関数が線形になるという意味ではない。
-- `dx ↦ 30 t^4 * dx` という線形写像になっていると思われる。
#check (fderiv ℝ (fun (t : ℝ) => 6 * t ^ 5)) t₀ rewrite_by fun_trans

-- 本にある解答。
-- `d/dt L` を表す。
-- `fun t => L t (y t)` を `t` に関して微分したもの。
#check ∂ (t:=t), L t (y t)

-- 本にある解答。
-- `∂/∂t L` を表す。
-- `fun t => L t (y t₀)` を `t` に関して微分した後で、`t₀ := t` としたもの。
#check ∂ (t:=t), L t (y t₀)
#check ∂ (t':=t), L t' (y t)

end

/- ## Exercise 4 (2つめ)

**TODO** Exercise 4 が２つあるのはどういう意図か？
-/
section



end
