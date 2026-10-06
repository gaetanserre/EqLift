/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.ForMathlib.MeasurableEquiv
public import EqLift.Kernel.Lift
public import EqLift.Tactic.Cache
public import Mathlib.Probability.Kernel.Composition.Prod
public import Mathlib.Probability.Kernel.Composition.CompProd
public meta import Qq

/-!
# Kernel lifting utilities

Utilities for lifting and unlifting kernel expressions, built with `Qq`.

## Main declarations

* `getTypesFromKernel`: the carrier types and universe levels of a kernel.
* `kernelLevel`: the universe level of a lifted kernel.
* `liftCarrier`: the lift of a measurable space and the measurable equivalence with its lift.
* `getOriginalType`: the original type of a lifted type.
* `unliftCarrier`: the same as `liftCarrier`, from the lifted space.
-/

public meta section

open Lean Meta Qq ProbabilityTheory

/-- Extract `(X, Y, u, v)` from an expression of type `Kernel X Y`. -/
def getTypesFromKernel (κ : Expr) : MetaM (Expr × Expr × Level × Level) := do
  let κType ← inferType κ
  let_expr Kernel X Y _ _ := κType | throwError "Expected a kernel type, got: {κType}."
  let .const _ [u, v] := κType.getAppFn | throwError "Expected a kernel type, got: {κType}."
  return (X, Y, u, v)

/-- Simplify the maxima `max l l` of a level, which appear in the universe levels of the products
of types living in the same universe `Type l`. -/
def dedupMaxLevel : Level → Level
  | .max a b =>
    let a := dedupMaxLevel a
    let b := dedupMaxLevel b
    if a == b then a else mkLevelMax a b
  | l => l

/-- The universe level `w` of the carriers of a lifted kernel `κ : Kernel X Y`: all the carriers of
a lifted equality live in `Type w`. -/
def kernelLevel (κ : Expr) : MetaM Level := do
  let (_, _, xLvl, _) ← getTypesFromKernel κ
  return dedupMaxLevel xLvl

/-- The lift `X'` of a measurable space `X : Type x` to the universe `w`, together with the
`MeasurableSpace` instances of `X` and `X'` and the measurable equivalence `X' ≃ᵐ X`. Products are
lifted componentwise, `PUnit` to `PUnit` and the other types to `ULift`. -/
partial def liftCarrier (w : Level) (X : Expr) :
    MetaM ((x : Level) × (X : Q(Type x)) × (_ : Q(MeasurableSpace $X)) × (X' : Q(Type w)) ×
      (_ : Q(MeasurableSpace $X')) × Q($X' ≃ᵐ $X)) := do
  let x ← getDecLevel X
  have X : Q(Type x) := X
  let mX ← synthInstanceQCached q(MeasurableSpace $X)
  let res ← memoized `liftCarrier (mkApp X (mkSort w)) do
    match_expr ← whnf X with
    | Prod A B =>
      let ⟨_, _, _, A', mA', eA⟩ ← liftCarrier w A
      let ⟨_, _, _, B', mB', eB⟩ ← liftCarrier w B
      return #[q($A' × $B'), q(@Prod.instMeasurableSpace $A' $B' $mA' $mB'),
        q(MeasurableEquiv.prodCongr $eA $eB)]
    | PUnit => return #[q(PUnit.{w + 1}),
        (q(PUnit.instMeasurableSpace) : Q(MeasurableSpace PUnit.{w + 1})),
        q(MeasurableEquiv.punit.{w, x})]
    | _ =>
      let mX' ← synthInstanceQCached q(MeasurableSpace (ULift.{w} $X))
      return #[q(ULift.{w} $X), mX', q(@MeasurableEquiv.ulift.{x, w} $X $mX)]
  return ⟨x, X, mX, res[0]!, res[1]!, res[2]!⟩

/-- Get the original type from a lifted type. `PUnit` is unlifted to `PUnit.{1}`, the target of
`Kernel.discard`. -/
partial def getOriginalType (t : Expr) : MetaM (Expr × Level) := do
  let t' ← whnf t
  match_expr t' with
  | PUnit => return (mkConst ``PUnit [Level.one], 0)
  | ULift X =>
    let .const _ [_, x] := t'.getAppFn | throwError "Expected a lifted type, got: {t}."
    return (X, x)
  | Prod A B =>
    let (A, a) ← getOriginalType A
    let (B, b) ← getOriginalType B
    have A : Q(Type a) := A
    have B : Q(Type b) := B
    return (q($A × $B), mkLevelMax a b)
  | _ => return (t, ← getDecLevel t)

/-- A lifted measurable space `X' : Type w` with its original space `X` (see `getOriginalType`),
their `MeasurableSpace` instances and the measurable equivalence `X' ≃ᵐ X` of `liftCarrier`. -/
def unliftCarrier (w : Level) (X' : Expr) :
    MetaM ((X' : Q(Type w)) × (_ : Q(MeasurableSpace $X')) × (x : Level) × (X : Q(Type x)) ×
      (_ : Q(MeasurableSpace $X)) × Q($X' ≃ᵐ $X)) := do
  let (X, _) ← getOriginalType X'
  let ⟨x, X, mX, _, mX', ex⟩ ← liftCarrier w X
  return ⟨X', (mX' : Expr), x, X, mX, (ex : Expr)⟩

end
