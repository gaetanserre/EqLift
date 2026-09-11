/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Lift
public import EqLift.Tactic.Kernel.Utils

/-!
# Implementation of the `lift_eq` tactic for kernels.

This file contains functions that propagate the lifting of kernel expressions through several
operators and primitives, and constructs the necessary proofs for the `lift_eq` tactic. Each
function returns the lifted expression `e'` together with a proof of `e' = e.lift`, built by
congruence from the compatibility lemmas of `Kernel.lift` (`comp_lift`, `parallelComp_lift`, ...).
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- The arguments shared by the compatibility lemmas of `Kernel.lift` for a kernel `Kernel X Y`:
`X [mX] Y [mY] X' [mX'] Y' [mY'] ex ey`. -/
def liftLemmaArgs (X Y X' Y' : Carrier) (ex ey : Expr) : MetaM (Array Expr) := do
  return #[X.1, ← X.inst, Y.1, ← Y.inst, X'.1, ← X'.inst, Y'.1, ← Y'.inst, ex, ey]

/-- Lifts a binary kernel operation by lifting the inner kernels. `mkOp` builds the operation
from the lifted kernels, and `pf` must be a proof of `mkOp κ.lift η.lift = (mkOp κ η).lift`. -/
def liftBinary (κ η : Expr) (maxLvl : Level) (mkOp : Expr → Expr → MetaM Expr) (pf : Expr) :
    MetaM (Expr × Expr) := do
  let (κ', pκ) ← liftExpr κ maxLvl
  let (η', pη) ← liftExpr η maxLvl
  let e' ← mkOp κ' η'
  let h ← mkCongr (← mkCongrArg e'.appFn!.appFn! pκ) pη
  return (e', ← mkEqTrans h pf)

/-- Lifts a composition of kernels by lifting the inner kernels. -/
def liftComposition (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  let η := args[args.size - 2]!
  let κ := args[args.size - 1]!
  let (X, Y) ← getCarriersFromKernel η
  let (Z, _) ← getCarriersFromKernel κ
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let (ez, Z') ← Z.lift maxLvl
  let pf := mkAppN (mkConst ``comp_lift [X.2, Y.2, Z.2, maxLvl]) <|
    (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.1, ← Z.inst, Z'.1, ← Z'.inst, ez, η, κ]
  liftBinary η κ maxLvl (mkKernelComp Z' X' Y') pf

initialize registerLiftExpr liftComposition

/-- Lifts a parallel composition of kernels by lifting the inner kernels. -/
def liftParallelComp (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y) ← getCarriersFromKernel κ
  let (Z, T) ← getCarriersFromKernel η
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let (ez, Z') ← Z.lift maxLvl
  let (et, T') ← T.lift maxLvl
  let pf := mkAppN (mkConst ``parallelComp_lift [X.2, Y.2, Z.2, maxLvl, T.2]) <|
    (← liftLemmaArgs X Y X' Y' ex ey) ++
      #[Z.1, ← Z.inst, T.1, ← T.inst, Z'.1, ← Z'.inst, T'.1, ← T'.inst, ez, et, κ, η]
  liftBinary κ η maxLvl (mkKernelParallelComp X' Y' Z' T') pf

initialize registerLiftExpr liftParallelComp

/-- Lifts a product of kernels by lifting the inner kernels. -/
def liftProd (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y) ← getCarriersFromKernel κ
  let (_, Z) ← getCarriersFromKernel η
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let (ez, Z') ← Z.lift maxLvl
  let pf := mkAppN (mkConst ``prod_lift [X.2, Y.2, Z.2, maxLvl]) <|
    (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.1, ← Z.inst, Z'.1, ← Z'.inst, ez, κ, η]
  liftBinary κ η maxLvl (mkKernelProd X' Y' Z') pf

initialize registerLiftExpr liftProd

/-- Lifts a composition-product of kernels by lifting the inner kernels. -/
def liftCompProd (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  let κ := args[args.size - 2]!
  let η := args[args.size - 1]!
  let (X, Y) ← getCarriersFromKernel κ
  let (_, Z) ← getCarriersFromKernel η
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let (ez, Z') ← Z.lift maxLvl
  let pf := mkAppN (mkConst ``compProd_lift [X.2, Y.2, Z.2, maxLvl]) <|
    (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.1, ← Z.inst, Z'.1, ← Z'.inst, ez, κ, η]
  liftBinary κ η maxLvl (mkKernelCompProd X' Y' Z') pf

initialize registerLiftExpr liftCompProd

/-- Lifts the identity kernel by lifting the carrier type. -/
def liftId (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X, _) ← getCarriersFromKernel e
  let (ex, X') ← X.lift maxLvl
  let pf := mkAppN (mkConst ``id_lift [X.2, maxLvl]) #[X.1, ← X.inst, X'.1, ← X'.inst, ex]
  return (← mkKernelId X', pf)

initialize registerLiftExpr liftId

/-- Lifts a discard kernel by lifting the carrier type. -/
def liftDiscard (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X, (_, punitLvl)) ← getCarriersFromKernel e
  let (ex, X') ← X.lift maxLvl
  let pf := mkAppN (mkConst ``discard_lift [X.2, maxLvl, punitLvl])
    #[X.1, ← X.inst, X'.1, ← X'.inst, ex]
  return (← mkKernelDiscard X' maxLvl, pf)

initialize registerLiftExpr liftDiscard

/-- Lifts a copy kernel by lifting the carrier type. -/
def liftCopy (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X, _) ← getCarriersFromKernel e
  let (ex, X') ← X.lift maxLvl
  let pf := mkAppN (mkConst ``copy_lift [X.2, maxLvl]) #[X.1, ← X.inst, X'.1, ← X'.inst, ex]
  return (← mkKernelCopy X', pf)

initialize registerLiftExpr liftCopy

/-- Lifts a swap kernel by lifting the carrier types. -/
def liftSwap (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let X : Carrier := (args[0]!, ← getDecLevel args[0]!)
  let Y : Carrier := (args[1]!, ← getDecLevel args[1]!)
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let pf := mkAppN (mkConst ``swap_lift [X.2, Y.2, maxLvl]) (← liftLemmaArgs X Y X' Y' ex ey)
  return (← mkKernelSwap X' Y', pf)

initialize registerLiftExpr liftSwap

/-- Lifts a kernel using `Kernel.lift`. -/
def liftKernel (e : Expr) (maxLvl : Level) : MetaM (Expr × Expr) := do
  let (X, Y) ← getCarriersFromKernel e
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  let e' ← mkKernelLift X Y X' Y' ex ey e
  return (e', ← mkEqRefl e')

initialize registerLiftExpr liftKernel

/-- The finisher for kernels: `κ = η ↔ κ.lift = η.lift`. -/
def finisherKernel (κ η : Expr) (maxLvl : Level) : MetaM Expr := do
  let (X, Y) ← getCarriersFromKernel κ
  let (ex, X') ← X.lift maxLvl
  let (ey, Y') ← Y.lift maxLvl
  return mkAppN (mkConst ``lift_congr [X.2, Y.2, maxLvl]) <|
    (← liftLemmaArgs X Y X' Y' ex ey) ++ #[κ, η]

initialize registerLiftFinisher finisherKernel

end
