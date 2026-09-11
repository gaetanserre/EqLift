/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Transform

/-!
# Lift and Unlift utilities

This file provides utility functions for lifting and unlifting equalities.

A lifting (resp. unlifting) function transforms an expression `e` into an expression `e'` living
in a common universe level (resp. in the original universe levels), together with a proof that
the expression in the common universe level is the lift of the other one: `e' = lift e` when
lifting, `e = lift e'` when unlifting. These proofs are combined by congruence to obtain the
equivalence between the original equality and the transformed one.
-/

public meta section

open Lean Elab Tactic Meta Parser.Tactic

/-- A type alias for lifting/unlifting functions. Given an expression and the common universe
level, return the transformed expression together with a proof that the expression living in the
common universe level is the lift of the other one. -/
abbrev liftMetadata := Expr → Level → MetaM (Expr × Expr)

/-- A type alias for finisher functions. Given the two sides `a b` of an equality living in the
original universe levels and the common universe level, return a proof of
`a = b ↔ lift a = lift b`. -/
abbrev finisherMetadata := Expr → Expr → Level → MetaM Expr

/-- Transforms an expression using the registered lifting/unlifting functions given in `impl_ref`.
Returns the first successful transformation along with its proof. -/
def transformExpr (e : Expr) (maxLvl : Level) (impl_ref : IO.Ref (Array liftMetadata)) :
    MetaM (Expr × Expr) := do
  let handlers ← impl_ref.get
  handlers.firstM (fun h => h e maxLvl) <|> throwError "No transform handler found for {e}."

/-- From `pl : a = c` and `pr : b = d`, build a proof of `(a = b) = (c = d)`. -/
def mkEqCongr (pl pr : Expr) : MetaM Expr := do
  let some (α, _, _) := (← inferType pl).eq? | throwError "Expected an equality, got: {pl}."
  let eqFn := mkApp (mkConst ``Eq [← getLevel α]) α
  mkCongr (← mkCongrArg eqFn pl) pr

/-- Constructs a proof of `(lhs = rhs) = (lhs_t = rhs_t)` from the proofs `pl pr` returned by the
lifting/unlifting functions for both sides and a finisher. When lifting, `pl : lhs_t = lift lhs`;
when unlifting, `pl : lhs = lift lhs_t` (and similarly for `pr`). -/
def constructProof (unlift : Bool) (lhs rhs lhs_t rhs_t pl pr : Expr) (maxLvl : Level)
    (finisher_ref : IO.Ref (Array finisherMetadata)) : MetaM Expr := do
  let (a, b) := if unlift then (lhs_t, rhs_t) else (lhs, rhs)
  let handlers ← finisher_ref.get
  let iff ← handlers.firstM (fun h => h a b maxLvl) <|> throwError "No finisher found for {a} = {b}."
  let congr ← mkEqCongr pl pr
  let propext ← mkPropExt iff
  if unlift then mkEqTrans congr (← mkEqSymm propext)
  else mkEqTrans propext (← mkEqSymm congr)

/-- Lifts or unlifts an equality expression by transforming both sides using the registered lifting/
unlifting functions. Returns the transformed equality and a proof of equality between the original
and transformed expressions. -/
def transformEquality (unlift : Bool) (getLvl : Expr → MetaM Level)
    (lift_ref : IO.Ref (Array liftMetadata)) (finisher_ref : IO.Ref (Array finisherMetadata))
    (eq : Expr) : MetaM (Expr × Expr) := do
  let e ← whnfR <| ← zetaReduce <| ← instantiateMVars eq
  let e := e.consumeMData
  let lvl ← getLvl eq
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}."
  let (lhs_transformed, pl) ← transformExpr lhs lvl lift_ref
  let (rhs_transformed, pr) ← transformExpr rhs lvl lift_ref
  let eq_transformed ← mkEq lhs_transformed rhs_transformed
  let proof ← constructProof unlift lhs rhs lhs_transformed rhs_transformed pl pr lvl finisher_ref
  return (eq_transformed, proof)

end
