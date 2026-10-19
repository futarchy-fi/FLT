/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelScalarExtension

/-!
# Rational coordinate functions of the original source kernel

The original x and y values descend as equivariant functions. The identity
idempotent distinguishes the infinity component, which cannot use the affine chart.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.Velu

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The x-coordinate of the actual source points as a rational algebra element. -/
def primeKernelX : PrimeKernelDescentAlgebra E p q hq hfixed := by
  letI := primeKernelLabelAction E p q hq hfixed
  refine ⟨fun i ↦ xCoord (primeKernelParam E p q hq i), ?_⟩
  intro g i
  change xCoord (primeKernelParam E p q hq (primeKernelLabelGalois E p q hq hfixed g i)) = _
  rw [primeKernelLabelGalois_point]
  exact xCoord_map E g _

/-- The y-coordinate of the actual source points as a rational algebra element. -/
def primeKernelY : PrimeKernelDescentAlgebra E p q hq hfixed := by
  letI := primeKernelLabelAction E p q hq hfixed
  refine ⟨fun i ↦ yCoord (primeKernelParam E p q hq i), ?_⟩
  intro g i
  change yCoord (primeKernelParam E p q hq (primeKernelLabelGalois E p q hq hfixed g i)) = _
  rw [primeKernelLabelGalois_point]
  exact yCoord_map E g _

/-- The infinity component is selected by a rational idempotent. -/
def primeKernelIdentity : PrimeKernelDescentAlgebra E p q hq hfixed := by
  letI := primeKernelLabelAction E p q hq hfixed
  refine ⟨fun i ↦ if i = 0 then 1 else 0, ?_⟩
  intro g i
  change (if primeKernelLabelGalois E p q hq hfixed g i = 0 then 1 else 0) =
    g (if i = 0 then 1 else 0)
  simp only [(primeKernelLabelGalois E p q hq hfixed g).map_eq_zero_iff]
  split_ifs <;> simp only [map_one, map_zero]

/-- Evaluation of the descended x function is its original geometric coordinate. -/
@[simp] theorem primeKernelX_evaluation (i : ZMod p) :
    primeKernelDescentEvaluation E p q hq hfixed i (primeKernelX E p q hq hfixed) =
      xCoord (primeKernelParam E p q hq i) := rfl

/-- Evaluation of the descended y function is its original geometric coordinate. -/
@[simp] theorem primeKernelY_evaluation (i : ZMod p) :
    primeKernelDescentEvaluation E p q hq hfixed i (primeKernelY E p q hq hfixed) =
      yCoord (primeKernelParam E p q hq i) := rfl

/-- Evaluation of the infinity function selects exactly the zero label. -/
@[simp] theorem primeKernelIdentity_evaluation (i : ZMod p) :
    primeKernelDescentEvaluation E p q hq hfixed i (primeKernelIdentity E p q hq hfixed) =
      if i = 0 then 1 else 0 := rfl

/-- Original evaluations jointly detect equality in the rational coordinate algebra. -/
@[ext] theorem primeKernelDescent_ext (a b : PrimeKernelDescentAlgebra E p q hq hfixed)
    (h : ∀ i, primeKernelDescentEvaluation E p q hq hfixed i a =
      primeKernelDescentEvaluation E p q hq hfixed i b) : a = b := by
  let _ := primeKernelLabelAction E p q hq hfixed
  exact MulActionHom.ext h

/-- The selected infinity component is open and closed at the algebra level. -/
theorem primeKernelIdentity_idempotent :
    IsIdempotentElem (primeKernelIdentity E p q hq hfixed) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  change (primeKernelIdentity E p q hq hfixed) * (primeKernelIdentity E p q hq hfixed) = _
  apply MulActionHom.ext
  intro i
  change (if i = 0 then (1 : AlgebraicClosure ℚ) else 0) *
    (if i = 0 then 1 else 0) = (if i = 0 then 1 else 0)
  split_ifs <;> simp

/-- The affine cubic relation includes the precise correction on the infinity component. -/
theorem primeKernel_affine_relation :
    let x := primeKernelX E p q hq hfixed
    let y := primeKernelY E p q hq hfixed
    let e := primeKernelIdentity E p q hq hfixed
    y ^ 2 + algebraMap ℚ _ E.a₁ * x * y + algebraMap ℚ _ E.a₃ * y =
      x ^ 3 + algebraMap ℚ _ E.a₂ * x ^ 2 + algebraMap ℚ _ E.a₄ * x +
        algebraMap ℚ _ E.a₆ * (1 - e) := by
  let _ := primeKernelLabelAction E p q hq hfixed
  dsimp only
  apply primeKernelDescent_ext E p q hq hfixed
  intro i
  simp only [map_add, map_mul, map_pow, map_sub, map_one, AlgHom.commutes,
    primeKernelX_evaluation, primeKernelY_evaluation, primeKernelIdentity_evaluation]
  by_cases hi : i = 0
  · subst i
    simp [map_zero, xCoord, yCoord]
  · rw [ite_eq_right hi, sub_zero, mul_one]
    cases hp : primeKernelParam E p q hq i with
    | zero =>
      exact False.elim (hi ((primeKernelParam_injective E p q hq)
        (hp.trans (map_zero _).symm)))
    | some x y h =>
      exact (WeierstrassCurve.Affine.equation_iff x y).mp h.left

end WeierstrassCurve.Velu
