/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Kernel.Lift
public import EqLift.Tactic.Lift
public import EqLift.Tactic.Kernel.Utils

/-!
# Implementation of the `lift_eq` tactic for kernels.

This file contains functions that propagate the lifting of kernel expressions through several
operators and primitives, and constructs the necessary proofs for the `lift_eq` tactic. Each
function returns the lifted expression `e'` together with a proof of `e' = e.lift`, built by
congruence from the compatibility lemmas of `Kernel.lift`.
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Lifts a binary kernel operation `op κ η` by lifting the inner kernels. `pf` must be a proof
of `op κ.lift η.lift = (op κ η).lift`. -/
def liftBinary (op : Name) (κ η : Expr) (maxLvl : Level) (pf : Expr) :
    MetaM (Expr × Expr) := do
  let (κ', pκ) ← liftExpr κ maxLvl
  let (η', pη) ← liftExpr η maxLvl
  let e' ← mkAppM op #[κ', η']
  let h ← mkCongr (← mkCongrArg e'.appFn!.appFn! pκ) pη
  return (e', ← mkEqTrans h pf)

/-- Lifts a composition of kernels by lifting the inner kernels. -/
def liftComposition (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  let η := args[args.size - 2]!
  let κ := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel η
  let (Z, _, tLvl, _) ← getTypesFromKernel κ
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z tLvl maxLvl
  liftBinary ``Kernel.comp η κ maxLvl (← mkAppM ``comp_lift #[ex, ey, ez, η, κ])

initialize registerLiftExpr liftComposition

/-- Lifts a parallel composition of kernels by lifting the inner kernels. -/
def liftParallelComp (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (Z, T, zLvl, tLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  let et ← constructMeasurableEquiv T tLvl maxLvl
  liftBinary ``Kernel.parallelComp κ η maxLvl
    (← mkAppM ``parallelComp_lift #[ex, ey, ez, et, κ, η])

initialize registerLiftExpr liftParallelComp

/-- Lifts a product of kernels by lifting the inner kernels. -/
def liftProd (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  liftBinary ``Kernel.prod κ η maxLvl (← mkAppM ``prod_lift #[ex, ey, ez, κ, η])

initialize registerLiftExpr liftProd

/-- Lifts a composition-product of kernels by lifting the inner kernels. -/
def liftCompProd (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let (_, Z, _, zLvl) ← getTypesFromKernel η
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let ez ← constructMeasurableEquiv Z zLvl maxLvl
  liftBinary ``Kernel.compProd κ η maxLvl (← mkAppM ``compProd_lift #[ex, ey, ez, κ, η])

initialize registerLiftExpr liftCompProd

/-- Lifts the identity kernel by lifting the carrier type. -/
def liftId (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let mX' ← synthInstance (mkApp (mkConst ``MeasurableSpace [maxLvl]) X')
  return (← mkAppOptM ``Kernel.id #[X', mX'], ← mkAppM ``id_lift #[ex])

initialize registerLiftExpr liftId

/-- Lifts a discard kernel by lifting the carrier type. -/
def liftDiscard (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X, _, xLvl, punitLvl) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let discard_lift_proof ← mkAppM' (mkConst ``discard_lift [xLvl, maxLvl, punitLvl]) #[ex]
  return (← mkAppOptM' (mkConst ``Kernel.discard [maxLvl, maxLvl]) #[X', none], discard_lift_proof)

initialize registerLiftExpr liftDiscard

/-- Lifts a copy kernel by lifting the carrier type. -/
def liftCopy (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X, _, xLvl, _) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  return (← mkAppOptM ``Kernel.copy #[X', none], ← mkAppM ``copy_lift #[ex])

initialize registerLiftExpr liftCopy

/-- Lifts a swap kernel by lifting the carrier types. -/
def liftSwap (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let X := args[0]!
  let Y := args[1]!
  let ex ← constructMeasurableEquiv X (← getDecLevel X) maxLvl
  let ey ← constructMeasurableEquiv Y (← getDecLevel Y) maxLvl
  let (X', _) ← getTypesFromMeasurableEquiv ex
  let (Y', _) ← getTypesFromMeasurableEquiv ey
  return (← mkAppOptM ``Kernel.swap #[X', Y', none, none], ← mkAppM ``swap_lift #[ex, ey])

initialize registerLiftExpr liftSwap

/-- Lifts a kernel using `Kernel.lift`. -/
def liftKernel (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel e
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  let e' ← mkAppOptM ``Kernel.lift #[none, none, none, none, none, none, none, none, ex, ey, e]
  return (e', ← mkEqRefl e')

initialize registerLiftExpr liftKernel

/-- The finisher for kernels: `κ = η ↔ κ.lift = η.lift`. -/
def finisherKernel (κ η : Expr) (maxLvl : Level) : MetaM Expr := do
  let (X, Y, xLvl, yLvl) ← getTypesFromKernel κ
  let ex ← constructMeasurableEquiv X xLvl maxLvl
  let ey ← constructMeasurableEquiv Y yLvl maxLvl
  mkAppM ``lift_congr #[ex, ey, κ, η]

initialize registerLiftFinisher finisherKernel

end
