/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import EqLift.Tactic.Unlift
public import EqLift.Tactic.Kernel.KernelLift
public meta import Qq

/-!
# Implementation of the `unlift_eq` tactic for kernels.

This file registers the unlifting of lifted kernel expressions for the `unlift_eq` tactic, with the
same lemmas as the lifting.

## Main declarations

* `unliftKernelExpr`: recursive unlifting of a lifted kernel expression.
* `unliftKernelQ`: its typed version, for given measurable equivalences.
-/

public meta section

open Lean Meta Qq ProbabilityTheory

/-- Typed version of the unlifting of a lifted kernel `κ' : Kernel X' Y'` by the registered
unlifting functions. Given the measurable equivalences `ex : X' ≃ᵐ X` and `ey : Y' ≃ᵐ Y` returns
`κ'`, the unlifted kernel `κ` and the proof of `κ' = κ.lift`. -/
def unliftKernelQ {x y w : Level} {X : Q(Type x)} {Y : Q(Type y)} {mX : Q(MeasurableSpace $X)}
    {mY : Q(MeasurableSpace $Y)} {X' Y' : Q(Type w)} {mX' : Q(MeasurableSpace $X')}
    {mY' : Q(MeasurableSpace $Y')} (ex : Q($X' ≃ᵐ $X)) (ey : Q($Y' ≃ᵐ $Y)) (κ' : Expr) :
    MetaM ((κ' : Q(Kernel $X' $Y')) × (κ : Q(Kernel $X $Y)) ×
      Q($κ' = Kernel.lift (ex := $ex) (ey := $ey) $κ)) := do
  let (κ, pκ) ← unliftExpr κ' w
  return ⟨κ', κ, pκ⟩

/-- Recursive unlifting of a kernel `e` lifted to the universe `w`. Returns the unlifted kernel
`e'` together with a proof of `e = e'.lift`. Each step is a single application of a lifting
lemma, given the unliftings of the subterms. -/
def unliftKernelExpr (w : Level) (e : Expr) : MetaM (Expr × Expr) := do
  match_expr e with
  | Kernel.comp X Y Z _ _ _ η κ =>
    let ⟨_, _, _, _, _, ex⟩ ← unliftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← unliftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← unliftCarrier w Z
    let ⟨_, κ, pκ⟩ ← unliftKernelQ ex ey κ
    let ⟨_, η, pη⟩ ← unliftKernelQ ey ez η
    return (q($η ∘ₖ $κ), q(Kernel.comp_lift_of_eq $pη $pκ))
  | Kernel.parallelComp X Y Z T _ _ _ _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← unliftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← unliftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← unliftCarrier w Z
    let ⟨_, _, _, _, _, et⟩ ← unliftCarrier w T
    let ⟨_, κ, pκ⟩ ← unliftKernelQ ex ey κ
    let ⟨_, η, pη⟩ ← unliftKernelQ ez et η
    return (q($κ ∥ₖ $η), q(Kernel.parallelComp_lift_of_eq $pκ $pη))
  | Kernel.prod X Y _ _ Z _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← unliftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← unliftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← unliftCarrier w Z
    let ⟨_, κ, pκ⟩ ← unliftKernelQ ex ey κ
    let ⟨_, η, pη⟩ ← unliftKernelQ ex ez η
    return (q($κ ×ₖ $η), q(Kernel.prod_lift_of_eq $pκ $pη))
  | Kernel.compProd X Y Z _ _ _ κ η =>
    let ⟨_, _, _, _, _, ex⟩ ← unliftCarrier w X
    let ⟨_, _, _, _, _, ey⟩ ← unliftCarrier w Y
    let ⟨_, _, _, _, _, ez⟩ ← unliftCarrier w Z
    let ⟨_, κ, pκ⟩ ← unliftKernelQ ex ey κ
    let ⟨_, η, pη⟩ ← unliftKernelQ q(MeasurableEquiv.prodCongr $ex $ey) ez η
    return (q($κ ⊗ₖ $η), q(Kernel.compProd_lift_of_eq $pκ $pη))
  | Kernel.id X _ =>
    let ⟨_, _, _, X, mX, ex⟩ ← unliftCarrier w X
    return (q(@Kernel.id $X $mX), q(Kernel.id_lift $ex))
  | Kernel.discard X _ =>
    let ⟨_, _, x, X, _, ex⟩ ← unliftCarrier w X
    return (q(Kernel.discard.{x, 0} $X), q(Kernel.discard_lift.{x, w, 0} $ex))
  | Kernel.copy X _ =>
    let ⟨_, _, _, X, _, ex⟩ ← unliftCarrier w X
    return (q(Kernel.copy $X), q(Kernel.copy_lift $ex))
  | Kernel.swap X Y _ _ =>
    let ⟨_, _, _, X, _, ex⟩ ← unliftCarrier w X
    let ⟨_, _, _, Y, _, ey⟩ ← unliftCarrier w Y
    return (q(Kernel.swap $X $Y), q(Kernel.swap_lift $ex $ey))
  | Kernel.lift _ _ _ _ _ _ _ _ _ _ κ => return (κ, ← mkEqRefl e)
  | _ => throwError "Expected a lifted kernel expression, got: {e}."

initialize registerUnliftExpr fun e w ↦ unliftKernelExpr (dedupMaxLevel w) e

initialize registerUnliftFinisher finisherKernel

end
