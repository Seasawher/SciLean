-- import SciLean.Analysis.Calculus.Notation.Deriv
-- import SciLean.Analysis.Scalar.Notation
import SciLean
import Batteries.Lean.Float --#
import Batteries.Data.Rat.Float --#

open SciLean Scalar

-- #synth NontriviallyNormedField Float
-- #synth DenselyNormedField Float
-- #check DenselyNormedField.toNontriviallyNormedField

set_default_scalar ℝ

/-- 分母が2のベキであるような正の有理数を10進小数として表示する -/
def Rat.pow2ToBase10Pos (x : Rat) : String :=
  -- 整数部分
  let integerPart := toString x.floor

  -- `x` の分母は `2ⁱ` という形をしていると仮定したので、その指数 `i` を求めておく
  let i := Nat.log2 x.den

  -- 小数部分を`x` の分母が `2ⁱ` であることを利用して計算する
  let decimalPart := (x.num % x.den) * 5 ^ i
    |> toString
    |>.leftpad i '0'

  integerPart ++ "." ++ decimalPart

/-- 分母が2のベキであるような有理数を10進小数として表示する -/
def Rat.pow2ToBase10 (x : Rat) : String :=
  if 0 ≤ x then x.pow2ToBase10Pos else "-" ++ (-x).pow2ToBase10Pos

/-- `Float` を丸めを行わずに正確に表示する -/
def Float.toExactDecimal (x : Float) : String := x.toRat0.pow2ToBase10

/-- `f(x) = x² - y` を解くことによって、Newton 法で `√y` を近似的に求める -/
def mySqrt (steps : Nat) (y : Float) : Float := Id.run do
  let f := fun x => x^2 - y
  let mut x := 1.0
  let df : Float → Float := fun x => ((deriv f x) rewrite_by fun_trans[deriv])
  for _ in [0 : steps] do
    x := x - f x / df x
  return x

-- df の計算が行われているのはいつなのか気になった。
-- この計算ができるということは、df を定義した時点で計算を終わらせていて、
-- for 文の中で計算するより早いかもね？
#check fun x => ((deriv (fun x : Float => x^2) x) rewrite_by fun_trans[deriv])

-- 10 以降は変化がないようだ
#eval Float.toExactDecimal <| mySqrt (steps := 4) 2.0

/- ## Exercises -/

/- ### Exercise 1.

try to solve different equations, for example `exp x = y` to obtain `log`, `x*exp x = y` to obtain Lambert `W` function or some polynomial.
-/

/-- Newton法を使って自前で実装した対数関数。-/
def myLog (y : Float) : Float := Id.run do
  let f := fun x => exp x - y
  let mut x := 1.0
  let df : Float → Float := fun x => ((deriv f x) rewrite_by fun_trans[deriv])
  while (f x).abs > 1.0e-7 do
    x := x - f x / df x
  return x

#eval myLog (exp 1.0)
#eval myLog (exp 2.0)
#eval myLog 3

def myLambertW (y : Float) : Float := Id.run do
  let f := fun x => x * exp x - y
  let mut x := 1.0
  let df : Float → Float := fun x => ((deriv f x) rewrite_by fun_trans[deriv])
  while (f x).abs > 1.0e-7 do
    x := x - f x / df x
  return x

#eval myLambertW 1.0
#eval myLambertW (exp 1.0)
