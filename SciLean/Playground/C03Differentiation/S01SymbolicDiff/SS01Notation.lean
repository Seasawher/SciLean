-- import SciLean
import SciLean.Analysis.Calculus.Notation.Deriv
import SciLean.Analysis.Scalar.Notation

open SciLean Scalar

-- 係数が実数であると宣言する
set_default_scalar ℝ

/- ## Exercise 1

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

/- ## Exercise 2

For `(g : ℝ×ℝ → ℝ)`, express derivative of `g (x,y)` in x.
-/
section

variable (n : Nat)
#check (∂ (x : ℝ), x^n) rewrite_by fun_trans

variable {g : ℝ × ℝ → ℝ} {x y : ℝ}

#check ∂ x, (g (x, y))

-- 具体的な g を当てはめてみて、解答が正しいか検証する
private abbrev g₁ : ℝ × ℝ → ℝ := fun (x, y) => x^2 + y^2

#check ∂ x, (g₁ (x, y)) rewrite_by fun_trans

#check
  -- **TODO**: 余計な let 式が出てこないようにできるか？
  let g : ℝ × ℝ → ℝ := fun (x, y) => x^2 + y^2
  ∂ x, (g (x, y)) rewrite_by fun_trans

end

/- ## Exercise 3

Express second derivatives of `f : ℝ → ℝ → ℝ` in the first and the second argument.
-/
section

variable {f : ℝ → ℝ → ℝ} {x y y₀ : ℝ}

-- 具体例
#check ∂! (x : ℝ), (∂! (x : ℝ), (x^2)) x

-- **TODO**: なぜ１が登場するのか？
-- rewrite_by が本来使われるべきでないケースで使ってるからバグってるのではないか。
#check ∂! x, (f x y)

#check ∂ x, (f x y)
#check ∂ x, (f x y₀)

-- `∂ x, (f x y)` は `y` に何か値を代入して固定値にしていて、だから `ℝ → ℝ` になる。
#check ∂ x, (f x y)
#check fun y => ∂ x, (f x y)

-- たぶんこれが答え
#check ∂ x, ((∂ x, (f x y)) x)
#check ∂ y, ((∂ y, (f x y)) y)

#check
  let g : ℝ → ℝ → ℝ := fun x y => x^2 + y^2
  ∂ x, ((∂ x, (g x y)) x) rewrite_by fun_trans

-- **TODO**: `∂!` を使うと結果が変わり、見づらい出力になるのはバグではないか？
#check
  let g : ℝ → ℝ → ℝ := fun x y => x^2 + y^2
  ∂! x, ((∂! x, (g x y)) x)

end
