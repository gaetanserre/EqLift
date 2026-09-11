/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Unlift
public import EqLift.Tactic.Kernel.KernelLift

/-!
# Implementation of the `unlift_eq` tactic for kernels.

This file contains functions that propagate the unlifting of lifted kernel expressions through
several operators and primitives, and constructs the necessary proofs for the `unlift_eq` tactic.
Each function returns the unlifted expression `e'` together with a proof of `e = e'.lift`, built by
congruence from the compatibility lemmas of `Kernel.lift` (`comp_lift`, `parallelComp_lift`, ...).
-/

public meta section

open Lean Meta Parser.Tactic ProbabilityTheory ProbabilityTheory.Kernel

/-- Unlifts a binary kernel operation `e = op κ' η'` by unlifting the inner kernels. `mkOp` builds
the operation from the unlifted kernels `κ η`, and `mkPf` must return a proof of
`op κ.lift η.lift = (op κ η).lift`. -/
def unliftBinary (e κ' η' : Expr) (eLvl : Level) (mkOp : Expr → Expr → MetaM Expr)
    (mkPf : Expr → Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let (κ, pκ) ← unliftExpr κ' eLvl
  let (η, pη) ← unliftExpr η' eLvl
  let h ← mkCongr (← mkCongrArg e.appFn!.appFn! pκ) pη
  return (← mkOp κ η, ← mkEqTrans h (← mkPf κ η))

/-- Unlifts a composition of kernels by unlifting the inner kernels. -/
def unliftComposition (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.comp do
    throwError "Expected a composition of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e args[args.size - 2]! args[args.size - 1]! eLvl
    (fun η κ => do
      let (X, Y) ← getCarriersFromKernel η
      let (Z, _) ← getCarriersFromKernel κ
      mkKernelComp Z X Y η κ)
    fun η κ => do
      let (X, Y) ← getCarriersFromKernel η
      let (Z, _) ← getCarriersFromKernel κ
      let (ex, X') ← X.lift eLvl
      let (ey, Y') ← Y.lift eLvl
      let (ez, Z') ← Z.lift eLvl
      return mkAppN (mkConst ``comp_lift [X.lvl, Y.lvl, Z.lvl, eLvl]) <|
        (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.type, ← Z.inst, Z'.type, ← Z'.inst, ez, η, κ]

initialize registerUnliftExpr unliftComposition

/-- Unlifts a parallel composition of kernels by unlifting the inner kernels. -/
def unliftParallelComp (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.parallelComp do
    throwError "Expected a parallel composition of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e args[args.size - 2]! args[args.size - 1]! eLvl
    (fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (Z, T) ← getCarriersFromKernel η
      mkKernelParallelComp X Y Z T κ η)
    fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (Z, T) ← getCarriersFromKernel η
      let (ex, X') ← X.lift eLvl
      let (ey, Y') ← Y.lift eLvl
      let (ez, Z') ← Z.lift eLvl
      let (et, T') ← T.lift eLvl
      return mkAppN (mkConst ``parallelComp_lift [X.lvl, Y.lvl, Z.lvl, eLvl, T.lvl]) <|
        (← liftLemmaArgs X Y X' Y' ex ey) ++
          #[Z.type, ← Z.inst, T.type, ← T.inst, Z'.type, ← Z'.inst, T'.type, ← T'.inst, ez, et, κ, η]

initialize registerUnliftExpr unliftParallelComp

/-- Unlifts a product of kernels by unlifting the inner kernels. -/
def unliftProd (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.prod do
    throwError "Expected a product of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e args[args.size - 2]! args[args.size - 1]! eLvl
    (fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (_, Z) ← getCarriersFromKernel η
      mkKernelProd X Y Z κ η)
    fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (_, Z) ← getCarriersFromKernel η
      let (ex, X') ← X.lift eLvl
      let (ey, Y') ← Y.lift eLvl
      let (ez, Z') ← Z.lift eLvl
      return mkAppN (mkConst ``prod_lift [X.lvl, Y.lvl, Z.lvl, eLvl]) <|
        (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.type, ← Z.inst, Z'.type, ← Z'.inst, ez, κ, η]

initialize registerUnliftExpr unliftProd

/-- Unlifts a composition-product of kernels by unlifting the inner kernels. -/
def unliftCompProd (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.compProd do
    throwError "Expected a composition of product of kernels, but got {e}."
  let args := e.getAppArgs
  unliftBinary e args[args.size - 2]! args[args.size - 1]! eLvl
    (fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (_, Z) ← getCarriersFromKernel η
      mkKernelCompProd X Y Z κ η)
    fun κ η => do
      let (X, Y) ← getCarriersFromKernel κ
      let (_, Z) ← getCarriersFromKernel η
      let (ex, X') ← X.lift eLvl
      let (ey, Y') ← Y.lift eLvl
      let (ez, Z') ← Z.lift eLvl
      return mkAppN (mkConst ``compProd_lift [X.lvl, Y.lvl, Z.lvl, eLvl]) <|
        (← liftLemmaArgs X Y X' Y' ex ey) ++ #[Z.type, ← Z.inst, Z'.type, ← Z'.inst, ez, κ, η]

initialize registerUnliftExpr unliftCompProd

/-- The original carrier of a lifted carrier. -/
def unliftCarrier (X' : Expr) : MetaM Carrier := do
  let (type, lvl) ← getOriginalType X'
  return ⟨type, lvl⟩

/-- Unlifts the identity kernel by unlifting the carrier type. -/
def unliftId (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.id do
    throwError "Expected the identity kernel, but got {e}."
  let (X', _) ← getCarriersFromKernel e
  let X ← unliftCarrier X'.type
  let (ex, X'') ← X.lift eLvl
  let pf := mkAppN (mkConst ``id_lift [X.lvl, eLvl]) #[X.type, ← X.inst, X''.type, ← X''.inst, ex]
  return (← mkKernelId X, pf)

initialize registerUnliftExpr unliftId

/-- Unlifts the discard kernel by unlifting the carrier type. -/
def unliftDiscard (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.discard do
    throwError "Expected the discard kernel, but got {e}."
  let (X', _) ← getCarriersFromKernel e
  let X ← unliftCarrier X'.type
  let (ex, X'') ← X.lift eLvl
  let pf := mkAppN (mkConst ``discard_lift [X.lvl, eLvl, Level.zero])
    #[X.type, ← X.inst, X''.type, ← X''.inst, ex]
  return (← mkKernelDiscard X 0, pf)

initialize registerUnliftExpr unliftDiscard

/-- Unlifts the copy kernel by unlifting the carrier type. -/
def unliftCopy (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.copy do
    throwError "Expected the copy kernel, but got {e}."
  let (X', _) ← getCarriersFromKernel e
  let X ← unliftCarrier X'.type
  let (ex, X'') ← X.lift eLvl
  let pf := mkAppN (mkConst ``copy_lift [X.lvl, eLvl]) #[X.type, ← X.inst, X''.type, ← X''.inst, ex]
  return (← mkKernelCopy X, pf)

initialize registerUnliftExpr unliftCopy

/-- Unlifts the swap kernel by unlifting the carrier types. -/
def unliftSwap (e : Expr) (eLvl : Level) : MetaM (Expr × Expr) := do
  unless e.isAppOf ``Kernel.swap do
    throwError "Expected the swap kernel, but got {e}."
  let args := e.getAppArgs
  let X ← unliftCarrier args[0]!
  let Y ← unliftCarrier args[1]!
  let (ex, X') ← X.lift eLvl
  let (ey, Y') ← Y.lift eLvl
  let pf := mkAppN (mkConst ``swap_lift [X.lvl, Y.lvl, eLvl]) (← liftLemmaArgs X Y X' Y' ex ey)
  return (← mkKernelSwap X Y, pf)

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
