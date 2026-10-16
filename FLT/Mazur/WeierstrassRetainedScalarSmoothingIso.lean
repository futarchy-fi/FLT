/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedDepthScale
public import FLT.Mazur.NodalFiberUnitScaling
public import FLT.Mazur.PolygonSmoothingReciprocalScaling

/-!
# The coefficient-scaled retained chart is an isomorphism

The fixed quotient changes the smoothing equation by a coefficient unit;
the independent depth scale rescales the two coordinates reciprocally.
Both operations act on the whole original node.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) (q α : Rˣ) (hq : π * (q : R) = τ)

/-- The full scalar model for the corrected retained chart. -/
def retainedScalarSmoothingEquiv : ChartRing τ ≃ₐ[R] ChartRing π :=
  ((NodalFiber.smoothingEquiv τ).symm.trans
    (NodalFiber.unitSmoothingEquiv τ π q hq.symm)).trans (reciprocalScaleEquiv π α⁻¹)

/-- The first coordinate includes the quotient and the inverse depth scale. -/
theorem retainedScalarSmoothingEquiv_left :
    retainedScalarSmoothingEquiv π τ q α hq (leftCoordinate τ) =
      algebraMap R (ChartRing π) (q : R) * leftCoordinate π *
        algebraMap R (ChartRing π) (↑α⁻¹ : R) := by
  change reciprocalScale π α⁻¹
    (NodalFiber.unitSmoothingEquiv τ π q hq.symm
      (NodalFiber.fromSmoothing τ (leftCoordinate τ))) = _
  rw [NodalFiber.fromSmoothing_left, NodalFiber.unitSmoothingEquiv_p,
    map_mul, AlgHom.commutes, reciprocalScale_left]
  ring

/-- The second coordinate retains the full coefficient depth scale. -/
theorem retainedScalarSmoothingEquiv_right :
    retainedScalarSmoothingEquiv π τ q α hq (rightCoordinate τ) =
      rightCoordinate π * algebraMap R (ChartRing π) (α : R) := by
  change reciprocalScale π α⁻¹
    (NodalFiber.unitSmoothingEquiv τ π q hq.symm
      (NodalFiber.fromSmoothing τ (rightCoordinate τ))) = _
  rw [NodalFiber.fromSmoothing_right, NodalFiber.unitSmoothingEquiv_q,
    reciprocalScale_right, inv_inv, mul_comm]

/-- With trivial root correction, the actual fixed-smoothing map is this equivalence. -/
theorem retainedScalarSmoothingEquiv_toAlgHom :
    (retainedScalarSmoothingEquiv π τ q α hq).toAlgHom =
      retainedFixedSmoothingEvaluation π τ (q : R) hq
        (retainedScaledCorrectionUnit π α 1) := by
  apply chartRing_hom_ext τ
  · rw [AlgEquiv.coe_toAlgHom,
      retainedScalarSmoothingEquiv_left, retainedFixedSmoothingEvaluation_left]
    simp only [retainedScaledCorrectionUnit, mul_one, ← map_inv]
    rfl
  · rw [AlgEquiv.coe_toAlgHom,
      retainedScalarSmoothingEquiv_right, retainedFixedSmoothingEvaluation_right]
    simp only [retainedScaledCorrectionUnit, mul_one]
    rfl

end FLT.Mazur.WeierstrassModificationX
