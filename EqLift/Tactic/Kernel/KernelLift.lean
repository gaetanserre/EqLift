/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Lift
public import EqLift.Tactic.Kernel.Utils
public meta import Qq

/-!
# Implementation of the `lift_eq` tactic for kernels.

This file registers the lifting of kernel expressions for the `lift_eq` tactic.

## Main declarations

* `liftKernelExpr`: recursive lifting of a kernel expression.
* `liftKernelQ`: its typed version, for given measurable equivalences.
* `finisherKernel`: the equivalence between an equality of kernels and the equality of their lifts.
-/

public meta section

open Lean Meta Qq ProbabilityTheory

/-- Typed version of the lifting of a kernel `κ : Kernel X Y` by the registered lifting functions.
Given the measurable equivalences `ex : X' ≃ᵐ X` and `ey : Y' ≃ᵐ Y` returns `κ`, its lift `κ'` and
the proof of `κ' = κ.lift`. -/
def liftKernelQ {x y w : Level} {X : Q(Type x)} {Y : Q(Type y)} {mX : Q(MeasurableSpace $X)}
    {mY : Q(MeasurableSpace $Y)} {X' Y' : Q(Type w)} {mX' : Q(MeasurableSpace $X')}
    {mY' : Q(MeasurableSpace $Y')} (ex : Q($X' ≃ᵐ $X)) (ey : Q($Y' ≃ᵐ $Y)) (κ : Expr) :
    MetaM ((κ : Q(Kernel $X $Y)) × (κ' : Q(Kernel $X' $Y')) ×
      Q($κ' = Kernel.lift (ex := $ex) (ey := $ey) $κ)) := do
  let (κ', pκ) ← liftExpr κ w
  return ⟨κ, κ', pκ⟩

/-- Recursive lifting of a kernel `e` to the universe `w`. Returns the lift `e'` together with a
proof of `e' = e.lift`. Each step is a single application of a lifting lemma, given the lifts
of the subterms. -/
def liftKernelExpr (w : Level) (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | Kernel.comp X Y Z _ _ _ η κ =>
    let ⟨_, _, _, _, _, ex⟩ ← liftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← liftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← liftCarrier w Z
    let ⟨_, κ', pκ⟩ ← liftKernelQ ex ey κ
    let ⟨_, η', pη⟩ ← liftKernelQ ey ez η
    return (q($η' ∘ₖ $κ'), q(Kernel.comp_lift_of_eq $pη $pκ))
  | Kernel.parallelComp X Y Z T _ _ _ _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← liftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← liftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← liftCarrier w Z
    let ⟨_, _, _, _, _, et⟩ ← liftCarrier w T
    let ⟨_, κ', pκ⟩ ← liftKernelQ ex ey κ
    let ⟨_, η', pη⟩ ← liftKernelQ ez et η
    return (q($κ' ∥ₖ $η'), q(Kernel.parallelComp_lift_of_eq $pκ $pη))
  | Kernel.prod X Y _ _ Z _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← liftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← liftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← liftCarrier w Z
    let ⟨_, κ', pκ⟩ ← liftKernelQ ex ey κ
    let ⟨_, η', pη⟩ ← liftKernelQ ex ez η
    return (q($κ' ×ₖ $η'), q(Kernel.prod_lift_of_eq $pκ $pη))
  | Kernel.compProd X Y Z _ _ _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← liftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← liftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← liftCarrier w Z
    let ⟨_, κ', pκ⟩ ← liftKernelQ ex ey κ
    let ⟨_, η', pη⟩ ← liftKernelQ q(MeasurableEquiv.prodCongr $ex $ey) ez η
    return (q($κ' ⊗ₖ $η'), q(Kernel.compProd_lift_of_eq $pκ $pη))
  | Kernel.id X _ =>
    let ⟨_, _, _, X', mX', ex⟩ ← liftCarrier w X
    return (q(@Kernel.id $X' $mX'), q(Kernel.id_lift $ex))
  | Kernel.discard X _ =>
    let .const _ [_, p] := e.getAppFn | throwError "Expected the discard kernel, got: {e}."
    let ⟨x, _, _, X', _, ex⟩ ← liftCarrier w X
    return (q(Kernel.discard.{w, w} $X'), q(Kernel.discard_lift.{x, w, p} $ex))
  | Kernel.copy X _ =>
    let ⟨_, _, _, X', _, ex⟩ ← liftCarrier w X
    return (q(Kernel.copy $X'), q(Kernel.copy_lift $ex))
  | Kernel.swap X Y _ _ =>
    let ⟨_, _, _, X', _, ex⟩ ← liftCarrier w X
    let ⟨_, _, _, Y', _, ey⟩ ← liftCarrier w Y
    return (q(Kernel.swap $X' $Y'), q(Kernel.swap_lift $ex $ey))
  | _ =>
    let (X, Y, _, _) ← getTypesFromKernel e
    let ⟨_, X, _, X', _, ex⟩ ← liftCarrier w X
    let ⟨_, Y, _, Y', _, ey⟩ ← liftCarrier w Y
    have e : Q(Kernel $X $Y) := e
    have e' : Q(Kernel $X' $Y') := q(Kernel.lift (ex := $ex) (ey := $ey) $e)
    return (e', q(Eq.refl $e'))

initialize registerLiftExpr fun e w ↦ liftKernelExpr w e

/-- The finisher for kernels: `(κ = η) = (κ' = η')` from `κ' = κ.lift` and `η' = η.lift`. -/
def finisherKernel (pl pr : Expr) : MetaM Expr :=
  mkAppM ``Kernel.lift_congr_of_eq #[pl, pr]

initialize registerLiftFinisher finisherKernel

end
