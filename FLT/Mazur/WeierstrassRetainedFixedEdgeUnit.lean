/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedDepthScale
public import FLT.Mazur.PolygonSmoothingUnitBoundary

/-!
# The exact unit on a fixed-smoothing retained edge

The outgoing parameter includes the global quotient, the coefficient scale,
and the entire root correction. The scale recurrence makes the next incoming
coordinate its inverse, without identifying different local smoothings.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π : R) (q : Rˣ) (U : (ChartRing π)ˣ)
local notation "L" => R[T;T⁻¹]
local notation "T₁" => LaurentUnitPoints.pointUnit (AlgHom.id R L)

/-- The outgoing Laurent unit retains both full correction and global quotient. -/
def retainedFixedEdgeUnit : Lˣ :=
  Units.map (algebraMap R L).toMonoidHom q * T₁ *
    (Units.map (leftLaurentMap π).toMonoidHom U)⁻¹

/-- The exact outgoing parameter has no discarded nilpotent terms. -/
theorem retainedFixedEdgeUnit_val :
    (retainedFixedEdgeUnit π q U : L) =
      algebraMap R L (q : R) * LaurentPolynomial.T 1 *
        leftLaurentMap π (↑U⁻¹ : ChartRing π) := rfl

variable (τ : R) (hq : π * (q : R) = τ)
local notation "F" => retainedFixedSmoothingEvaluation π τ (q : R) hq U

/-- The full fixed-smoothing map has precisely the constructed outgoing unit. -/
theorem retainedFixedSmoothingEvaluation_outgoing :
    leftLaurentMap π (F (leftCoordinate τ)) = (retainedFixedEdgeUnit π q U : L) := by
  rw [retainedFixedSmoothingEvaluation_left, map_mul, map_mul, AlgHom.commutes,
    leftLaurentMap_left, retainedFixedEdgeUnit_val]

/-- The preceding root evaluation is the original polygon preceding Laurent map. -/
theorem retainedPrecedingEvaluation_eq :
    retainedPrecedingEvaluation π = precedingLaurentMap R π := rfl

variable (α : Rˣ) (V V' : (ChartRing π)ˣ)
  (hV : Units.map (leftLaurentMap π).toMonoidHom V =
    Units.map (retainedPrecedingEvaluation π).toMonoidHom V')
local notation "U₀" => retainedScaledCorrectionUnit π α V
local notation "U₁" => retainedScaledCorrectionUnit π (α * q⁻¹) V'

include hV in
/-- The next incoming unit is the inverse of the exact outgoing unit. -/
theorem retainedFixedEdgeUnit_adjacent :
    T₁⁻¹ * Units.map (retainedPrecedingEvaluation π).toMonoidHom U₁ =
      (retainedFixedEdgeUnit π q U₀)⁻¹ := by
  rw [retainedScaledCorrectionUnit_adjacent π q α V V' hV, retainedFixedEdgeUnit,
    mul_inv_rev, mul_inv_rev, inv_inv, map_inv]
  simp only [mul_assoc, mul_comm]

include hV in
/-- Both full node maps give reciprocal coordinates at the original adjacent edge. -/
theorem retainedFixedSmoothingEvaluation_incoming :
    retainedPrecedingEvaluation π
        (retainedFixedSmoothingEvaluation π τ (q : R) hq U₁ (rightCoordinate τ)) =
      (↑(retainedFixedEdgeUnit π q U₀)⁻¹ : L) := by
  rw [retainedFixedSmoothingEvaluation_right, map_mul, retainedPrecedingEvaluation_right]
  exact congrArg Units.val (retainedFixedEdgeUnit_adjacent π q α V V' hV)

end FLT.Mazur.WeierstrassModificationX
