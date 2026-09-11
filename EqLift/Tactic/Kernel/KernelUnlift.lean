/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Kernel.Lift
public import EqLift.Tactic.Unlift
public import EqLift.Tactic.Kernel.KernelLift

/-!
# Implementation of the `unlift_eq` tactic for kernels.

This file contains functions that propagate the unlifting of lifted kernel expressions through
several operators and primitives, and constructs the necessary proofs for the `unlift_eq` tactic.
Each function returns the unlifted expression `e'` together with a proof of `e = e'.lift`, built by
congruence from the compatibility lemmas of `Kernel.lift`.
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Unlifts a binary kernel operation `e = op κ' η'` by unlifting the inner kernels. `mkLemma`
receives the unlifted kernels `κ η` and must return a proof of `op κ.lift η.lift = (op κ η).lift`.
-/
def unliftBinary (e : Expr) (op : Name) (κ' η' : Expr) (eLvl : Level)
    (mkLemma : Expr → Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let (κ, pκ) ← unliftExpr κ' eLvl
  let (η, pη) ← unliftExpr η' eLvl
  let h ← mkCongr (← mkCongrArg e.appFn!.appFn! pκ) pη
  return (← mkAppM op #[κ, η], ← mkEqTrans h (← mkLemma κ η))

/-- Unlifts a composition of kernels by unlifting the inner kernels. -/
def unliftComposition (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e ``Kernel.comp args[args.size - 2]! args[args.size - 1]! eLvl fun η κ => do
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
    let (Z, _, tLvl, _) ← getTypesFromKernel κ
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z tLvl eLvl
    mkAppM ``comp_lift #[ex, ey, ez, η, κ]

initialize registerUnliftExpr unliftComposition

/-- Unlifts a parallel composition of kernels by unlifting the inner kernels. -/
def unliftParallelComp (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e ``Kernel.parallelComp args[args.size - 2]! args[args.size - 1]! eLvl fun κ η => do
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    let et ← constructMeasurableEquiv T tLvl eLvl
    mkAppM ``parallelComp_lift #[ex, ey, ez, et, κ, η]

initialize registerUnliftExpr unliftParallelComp

/-- Unlifts a product of kernels by unlifting the inner kernels. -/
def unliftProd (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e ``Kernel.prod args[args.size - 2]! args[args.size - 1]! eLvl fun κ η => do
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (_, Z, _, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    mkAppM ``prod_lift #[ex, ey, ez, κ, η]

initialize registerUnliftExpr unliftProd

/-- Unlifts a composition-product of kernels by unlifting the inner kernels. -/
def unliftCompProd (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e ``Kernel.compProd args[args.size - 2]! args[args.size - 1]! eLvl fun κ η => do
    let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
    let (_, Z, _, zLvl) ← getTypesFromKernel η
    let ex ← constructMeasurableEquiv X xLvl eLvl
    let ey ← constructMeasurableEquiv Y yLvl eLvl
    let ez ← constructMeasurableEquiv Z zLvl eLvl
    mkAppM ``compProd_lift #[ex, ey, ez, κ, η]

initialize registerUnliftExpr unliftCompProd

/-- Unlifts the identity kernel by unlifting the carrier type. -/
def unliftId (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let mX ← synthInstance (mkApp (mkConst ``MeasurableSpace [xLvl]) X)
  return (← mkAppOptM ``Kernel.id #[X, mX], ← mkAppM ``id_lift #[ex])

initialize registerUnliftExpr unliftId

/-- Unlifts the discard kernel by unlifting the carrier type. -/
def unliftDiscard (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let discard_unlift_proof ← mkAppM' (mkConst ``discard_lift [xLvl, eLvl, Level.zero]) #[ex]
  return (← mkAppOptM' (mkConst ``Kernel.discard [xLvl, 0]) #[X, none], discard_unlift_proof)

initialize registerUnliftExpr unliftDiscard

/-- Unlifts the copy kernel by unlifting the carrier type. -/
def unliftCopy (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X', _, _, _) ← getTypesFromKernel e
  let (X, xLvl) ← getOriginalType X'
  let ex ← constructMeasurableEquiv X xLvl eLvl
  return (← mkAppOptM ``Kernel.copy #[X, none], ← mkAppM ``copy_lift #[ex])

initialize registerUnliftExpr unliftCopy

/-- Unlifts the swap kernel by unlifting the carrier types. -/
def unliftSwap (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let (X, xLvl) ← getOriginalType args[0]!
  let (Y, yLvl) ← getOriginalType args[1]!
  let ex ← constructMeasurableEquiv X xLvl eLvl
  let ey ← constructMeasurableEquiv Y yLvl eLvl
  return (← mkAppOptM ``Kernel.swap #[X, Y, none, none], ← mkAppM ``swap_lift #[ex, ey])

initialize registerUnliftExpr unliftSwap

/-- Unlifts a lifted kernel by returning the inner kernel. -/
def unliftKernel (e : Expr) (_ : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.lift do
    throwError "Expected a lifted kernel, but got {e}."
  let args := e.getAppArgs
  return (args[args.size - 1]!, ← mkEqRefl e)

initialize registerUnliftExpr unliftKernel

initialize registerUnliftFinisher finisherKernel

end
