/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public meta import Lean.Meta.AppBuilder
public meta import Lean.Meta.Transform
public import EqLift.Tactic.Cache

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

/-- A type alias for finisher functions. Given the proofs `pl : a' = lift a` and `pr : b' = lift b`
returned by the lifting/unlifting functions for both sides of an equality `a = b` living in the
original universe levels, return a proof of `(a = b) = (a' = b')`. -/
abbrev finisherMetadata := Expr → Expr → MetaM Expr

/-- Transforms an expression using the registered lifting/unlifting functions given in `impl_ref`.
Returns the first successful transformation along with its proof. -/
def transformExpr (e : Expr) (maxLvl : Level) (impl_ref : IO.Ref (Array liftMetadata)) :
    MetaM (Expr × Expr) := do
  let handlers ← impl_ref.get
  handlers.firstM (fun h => h e maxLvl) <|> throwError "No transform handler found for {e}."

/-- Constructs a proof of `(lhs = rhs) = (lhs_t = rhs_t)` from the proofs `pl pr` returned by the
lifting/unlifting functions for both sides and a finisher. When lifting, `pl : lhs_t = lift lhs`;
when unlifting, `pl : lhs = lift lhs_t` (and similarly for `pr`). -/
def constructProof (unlift : Bool) (pl pr : Expr) (finisher_ref : IO.Ref (Array finisherMetadata)) :
    MetaM Expr := do
  let handlers ← finisher_ref.get
  let pf ← handlers.firstM (fun h => h pl pr) <|> throwError "No finisher found for {pl}, {pr}."
  if unlift then mkEqSymm pf else return pf

/-- Lifts or unlifts an equality expression by transforming both sides using the registered lifting/
unlifting functions. Returns the transformed equality and a proof of equality between the original
and transformed expressions. -/
def transformEquality (unlift : Bool) (getLvl : Expr → MetaM Level)
    (lift_ref : IO.Ref (Array liftMetadata)) (finisher_ref : IO.Ref (Array finisherMetadata))
    (eq : Expr) : MetaM (Expr × Expr) := do
  resetTransformCache
  let e ← whnfR <| ← zetaReduce <| ← instantiateMVars eq
  let e := e.consumeMData
  let lvl ← getLvl eq
  let some (_, lhs, rhs) := e.eq? | throwError "Expected an equality, got: {e}."
  let (lhs_transformed, pl) ← transformExpr lhs lvl lift_ref
  let (rhs_transformed, pr) ← transformExpr rhs lvl lift_ref
  let eq_transformed ← mkEq lhs_transformed rhs_transformed
  let proof ← constructProof unlift pl pr finisher_ref
  return (eq_transformed, proof)

end
