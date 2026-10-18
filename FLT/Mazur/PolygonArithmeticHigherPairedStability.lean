/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticHigherCorrectionStability

/-!
# Stabilization of paired and rebased higher corrections

Both scalar drifts and both complete branch substitutions vanish on earlier
arithmetic quotients. Rebasing and inversion preserve this exact identity.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable (R : Type*) [CommRing R] (π : R)
  (m r : ℕ) (hm : m ≤ r) (t : Quotient R π m) (q : Bool → R[T;T⁻¹])
local notation "v" => fun b ↦ higherCorrectionField R π r (q b)

include hm

/-- Both successive higher smoothing drifts vanish on every earlier quotient. -/
theorem twoBranchCorrectionSmoothing_higher_stable :
    twoBranchCorrectionSmoothing R π m t v = t := by
  simp only [twoBranchCorrectionSmoothing, correctionSmoothing_higher_stable R π m r hm]

/-- The whole product of scalar drift units is one on every earlier quotient. -/
theorem twoBranchCorrectionDriftUnit_higher_stable :
    twoBranchCorrectionDriftUnit R π m v = 1 := by
  apply Units.ext
  simp only [twoBranchCorrectionDriftUnit, Units.val_mul, nilpotentMultiplier_val,
    higherCorrection_scalar_eq_zero R π m r hm, add_zero, mul_one, Units.val_one]

/-- The actual rebased terminal smoothing is unchanged on every earlier quotient. -/
theorem twoBranchCorrectionRebasedSmoothing_higher_stable :
    twoBranchCorrectionRebasedSmoothing R π m t v = t := by
  rw [twoBranchCorrectionRebasedSmoothing,
    twoBranchCorrectionDriftUnit_higher_stable R π m r hm, inv_one, Units.val_one, one_mul]

/-- Both complete punctures of the shared two-branch factor stabilize simultaneously. -/
theorem twoBranchCorrectionPunctureFactor_higher_stable (b : Bool) :
    twoBranchCorrectionPunctureFactor R π m t v b = AlgEquiv.refl := by
  rw [twoBranchCorrectionPunctureFactor,
    correctionPunctureFactor_higher_stable R π m r hm,
    correctionPunctureFactor_higher_stable R π m r hm]
  rfl

/-- Rebasing leaves both entire terminal substitutions stationary. -/
theorem twoBranchCorrectionRebasedPunctureFactor_higher_stable (b : Bool) :
    twoBranchCorrectionRebasedPunctureFactor R π m t v b = AlgEquiv.refl :=
  twoBranchCorrectionPunctureFactor_higher_stable R π m r hm _ q b

/-- Inverting the rebased terminal substitution preserves its full identity. -/
theorem twoBranchCorrectionRebasedPunctureFactor_higher_symm_stable (b : Bool) :
    (twoBranchCorrectionRebasedPunctureFactor R π m t v b).symm = AlgEquiv.refl := by
  rw [twoBranchCorrectionRebasedPunctureFactor_higher_stable R π m r hm]
  rfl

end FLT.Mazur.PolygonArithmeticStages
