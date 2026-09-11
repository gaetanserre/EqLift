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

/-!
# Kernel lifting utilities

This file provides helper functions for lifting and unlifting kernel expressions: type extraction,
construction of measurable equivalences, and explicit constructors for kernel operations and
`Kernel.lift`. The constructors build the applications directly (`mkAppN` with explicit universe
levels and instances) instead of going through `mkAppM`, whose unification is the main cost of
the transformations.

## Main declarations

* `Carrier`: a measurable space `X : Type u`, given by the expression `X` and the level `u`.
* `getTypesFromKernel`: extracts carrier types and universe levels from kernel expressions.
* `constructMeasurableEquiv`: recursively builds measurable equivalences.
* `getOriginalType`: retrieves the original type from a lifted type.
* `mkKernelComp`, `mkKernelParallelComp`, ..., `mkKernelLift`: explicit constructors.
-/

public meta section

open Lean Meta ProbabilityTheory Elab Term

/-- A measurable space: the carrier type and its universe level. -/
structure Carrier where
  /-- The carrier type. -/
  type : Expr
  /-- The universe level of the carrier type. -/
  lvl : Level

/-- The `MeasurableSpace` instance of a carrier (cached). -/
def Carrier.inst (c : Carrier) : MetaM Expr :=
  synthInstanceCached (mkApp (mkConst ``MeasurableSpace [c.lvl]) c.type)

/-- Extract `(X, Y, u, v)` from an expression of type `Kernel X Y`. -/
def getTypesFromKernel (κ : Expr) : MetaM (Expr × Expr × Level × Level) := do
  let κType ← inferTypeCached κ
  match κType.getAppFn with
  | Expr.const ``Kernel univs =>
    let args := κType.getAppArgs
    if args.size < 2 then
      throwError "Kernel type with insufficient arguments: {κType}."
    return (args[0]!, args[1]!, univs[0]!, univs[1]!)
  | _ => throwError "Expected a kernel type, got: {κType}."

/-- Extract the source and target carriers of a kernel. -/
def getCarriersFromKernel (κ : Expr) : MetaM (Carrier × Carrier) := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  return (⟨X, xLvl⟩, ⟨Y, yLvl⟩)

/-- Build the measurable equivalence `X' ≃ᵐ X` between the lift `X'` of `e` to the universe
`maxLvl` and `e` itself, recursively on products. Returns the equivalence and `X'`. -/
partial def constructMeasurableEquiv (e : Expr) (eLevel maxLvl : Level) : MetaM (Expr × Expr) := do
  let res ← memoized `constructMeasurableEquiv (mkApp e (mkSort maxLvl)) do
    let ewhnf ← whnf e
    match ewhnf.getAppFn with
    | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
      return #[mkConst ``MeasurableEquiv.punit [maxLvl, eLevel], mkConst ``PUnit [maxLvl.succ]]
    | Expr.const ``Prod [xLvl, yLvl] =>
      let args := ewhnf.getAppArgs
      let X := args[0]!
      let Y := args[1]!
      let (ex, X') ← constructMeasurableEquiv X xLvl maxLvl
      let (ey, Y') ← constructMeasurableEquiv Y yLvl maxLvl
      let equiv := mkAppN (mkConst ``MeasurableEquiv.prodCongr [maxLvl, xLvl, maxLvl, yLvl])
        #[X', X, Y', Y, ← Carrier.inst ⟨X', maxLvl⟩, ← Carrier.inst ⟨X, xLvl⟩,
          ← Carrier.inst ⟨Y', maxLvl⟩, ← Carrier.inst ⟨Y, yLvl⟩, ex, ey]
      return #[equiv, mkApp2 (mkConst ``Prod [maxLvl, maxLvl]) X' Y']
    | _ =>
      let equiv := mkAppN (mkConst ``MeasurableEquiv.ulift [eLevel, maxLvl])
        #[e, ← Carrier.inst ⟨e, eLevel⟩]
      return #[equiv, mkApp (mkConst ``ULift [maxLvl, eLevel]) e]
  return (res[0]!, res[1]!)

/-- Same as `constructMeasurableEquiv`, for a carrier. -/
def Carrier.lift (c : Carrier) (maxLvl : Level) : MetaM (Expr × Carrier) := do
  let (equiv, c') ← constructMeasurableEquiv c.type c.lvl maxLvl
  return (equiv, ⟨c', maxLvl⟩)

/-- Get the original type from a lifted type. -/
partial def getOriginalType (t : Expr) : MetaM (Expr × Level) := do
  let twhnf ← whnf t
  match twhnf.getAppFn with
  | Expr.const ``PUnit _ | Expr.const ``Unit _ =>
    return (mkConst ``Unit [], 0)
  | Expr.const ``ULift univs =>
    return (twhnf.getAppArgs[0]!, univs[1]!)
  | Expr.const ``Prod _ =>
    let args := twhnf.getAppArgs
    let (X, xLvl) ← getOriginalType args[0]!
    let (Y, yLvl) ← getOriginalType args[1]!
    return (mkApp2 (mkConst ``Prod [xLvl, yLvl]) X Y, .max xLvl yLvl)
  | _ =>
    return (t, ← getDecLevel (← inferTypeCached t))

/-! ### Explicit constructors -/

/-- `η ∘ₖ κ` with `κ : Kernel X Y` and `η : Kernel Y Z`. -/
def mkKernelComp (X Y Z : Carrier) (η κ : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.comp [X.lvl, Y.lvl, Z.lvl])
    #[X.type, Y.type, Z.type, ← X.inst, ← Y.inst, ← Z.inst, η, κ]

/-- `κ ∥ₖ η` with `κ : Kernel X Y` and `η : Kernel Z T`. -/
def mkKernelParallelComp (X Y Z T : Carrier) (κ η : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.parallelComp [X.lvl, Y.lvl, Z.lvl, T.lvl])
    #[X.type, Y.type, Z.type, T.type, ← X.inst, ← Y.inst, ← Z.inst, ← T.inst, κ, η]

/-- `κ ×ₖ η` with `κ : Kernel X Y` and `η : Kernel X Z`. -/
def mkKernelProd (X Y Z : Carrier) (κ η : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.prod [X.lvl, Y.lvl, Z.lvl])
    #[X.type, Y.type, ← X.inst, ← Y.inst, Z.type, ← Z.inst, κ, η]

/-- `κ ⊗ₖ η` with `κ : Kernel X Y` and `η : Kernel (X × Y) Z`. -/
def mkKernelCompProd (X Y Z : Carrier) (κ η : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.compProd [X.lvl, Y.lvl, Z.lvl])
    #[X.type, Y.type, Z.type, ← X.inst, ← Y.inst, ← Z.inst, κ, η]

/-- `Kernel.id : Kernel X X`. -/
def mkKernelId (X : Carrier) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.id [X.lvl]) #[X.type, ← X.inst]

/-- `Kernel.copy X`. -/
def mkKernelCopy (X : Carrier) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.copy [X.lvl]) #[X.type, ← X.inst]

/-- `Kernel.discard X : Kernel X PUnit.{punitLvl + 1}`. -/
def mkKernelDiscard (X : Carrier) (punitLvl : Level) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.discard [X.lvl, punitLvl]) #[X.type, ← X.inst]

/-- `Kernel.swap X Y`. -/
def mkKernelSwap (X Y : Carrier) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.swap [X.lvl, Y.lvl]) #[X.type, Y.type, ← X.inst, ← Y.inst]

/-- `κ.lift (ex := ex) (ey := ey) : Kernel X' Y'` with `κ : Kernel X Y`. -/
def mkKernelLift (X Y X' Y' : Carrier) (ex ey κ : Expr) : MetaM Expr := do
  return mkAppN (mkConst ``Kernel.lift [X.lvl, Y.lvl, X'.lvl])
    #[X.type, ← X.inst, Y.type, ← Y.inst, X'.type, ← X'.inst, Y'.type, ← Y'.inst, ex, ey, κ]

end
