import SciLean

open SciLean Scalar

-- 係数が実数であると宣言する
set_default_scalar ℝ

/- ## Exercise

Express first derivative of `f : ℝ → ℝ → ℝ` in the first and the second argument. Also express derivative in both arguments at the same time.
-/

section

variable {f : ℝ → ℝ → ℝ} {x y : ℝ}

-- 第一引数に対する偏微分
#check ∂ x, (f x y)

-- 第二引数に対する偏微分
#check ∂ y, (f x y)

-- 両引数に対する偏微分
#check ∂ ((x, y) : ℝ × ℝ), (f x y)

variable (x₀ y₀ : ℝ)
-- 解答にある例
#check ∂ (x:=x₀), (f x y₀)
#check ∂ (f · y₀) x₀

end
