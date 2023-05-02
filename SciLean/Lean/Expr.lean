import Lean
import Qq

namespace Lean.Expr


def explicitArgIds (e : Expr) : Array Nat := 
  run e #[] 0
where run (e : Expr) (ids : Array Nat) (i : Nat) : Array Nat := 
  match e with
  | .forallE _ _ e' bi => 
    if bi.isExplicit then 
      run e' (ids.push i) (i+1)
    else 
      run e' ids (i+1)
  | .lam _ _ e' bi => 
    if bi.isExplicit then 
      run e' (ids.push i) (i+1)
    else 
      run e' ids (i+1)
  | _ => ids

partial def flattenLet? (e : Expr) : Option Expr := do
  match e with
  | .letE xName xType xVal xBody _ => 
    match xVal with
    | .letE yName yType yVal yBody _ =>

      let e' := 
        .letE yName yType yVal
          (.letE xName xType yBody (xBody.liftLooseBVars 1 1) default) default

      return (flattenLet? e').getD e'

    | _ => do
      return (.letE xName xType xVal (← flattenLet? xBody) default)
  | _ => none


partial def flattenLet (e : Expr) : Expr := e.flattenLet?.getD e


partial def splitLetProd? (e : Expr) : Option Expr := do
  match e with
  | .letE xyName xyType xyVal xyBody _ =>
    if let .some (X,Y,x,y) := xyVal.app4? ``Prod.mk then
      
      let xy := mkApp4 xyVal.getAppFn X Y (.bvar 1) (.bvar 0)
      let e' := 
        Expr.letE (xyName.appendAfter "₁") X x
          (.letE (xyName.appendAfter "₂") Y y ((xyBody.liftLooseBVars 1 2).instantiate1 xy) default) default

      return (splitLetProd? e').getD e'
    else do
      return (.letE xyName xyType xyVal (← splitLetProd? xyBody) default)
  | _ => none

partial def splitLetProd (e : Expr) : Option Expr := e.splitLetProd?.getD e



/--
  Swaps bvars indices `i` and `j`

  NOTE: the indices `i` and `j` do not correspond to the `n` in `bvar n`. Rather
  they behave like indices in `Expr.lowerLooseBVars`, `Expr.liftLooseBVars`, etc.

  TODO: This has to have a better implementation, but I'm still beyond confused with how bvar indices work
-/
def swapBVars (e : Expr) (i j : Nat) : Expr := 

  let swapBVarArray : Array Expr := Id.run do
    let mut a : Array Expr := .mkEmpty e.looseBVarRange
    for k in [0:e.looseBVarRange] do
      a := a.push (.bvar (if k = i then j else if k = j then i else k))
    a

  e.instantiate swapBVarArray


def myPrint : Expr → String 
| .const n _ => n.toString
| .bvar n => s!"[{n}]"
| .app f x => f.myPrint ++ " " ++ x.myPrint
| .lam n t x bi => s!"fun {n} => {x.myPrint}"
| .letE n t v x _ => s!"let {n} := {v.myPrint}; {x.myPrint}"
| _ => "??"



#exit

open Qq
#eval show MetaM Unit from do

      
  let e := q(let ab := (1,2)
             let x  := 5
             let cd := (7,42,666)
             ab.1 + x + cd.2.1)

  if let some e' := e.splitLetProd? then

    IO.println (← Meta.ppExpr e')

    IO.println ""

    if let some e' := e'.splitLetProd? then

      IO.println (← Meta.ppExpr e')
