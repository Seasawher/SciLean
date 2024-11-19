import SciLean

open SciLean


/--
info: false
-/
#guard_msgs in
open Lean Meta Qq in
#eval show MetaM Unit from do

  let X : Q(Type) := q(Float → DataArrayN Float (Fin 10))
  withLocalDeclQ `x default X fun x => do
  let HX := q(Differentiable Float $x)
  withLocalDeclQ `hx default HX fun hx => do

  let H  := q(Differentiable Float fun w => ⊞ i => ($x w)[i])
  let h ← mkFreshExprMVar (H : Expr)
  IO.println (← isDefEq hx h)

-- TODO: fix index access herel
example
  (x : Float → DataArrayN Float (Fin 10)) (hx : Differentiable Float x)
  : Differentiable Float (fun w => ⊞ (i : Fin 10) => (x w)[i]) :=
by
  fun_prop