/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedEdgeUnit

/-!
# Full outgoing parameters after iterating the depth recurrence

The coefficient of the outgoing unit is q^(i+1), not q. The inverse
parameter is the one that must be compared with either terminal puncture.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
variable {R : Type*} [CommRing R] (π : R) (q α : Rˣ)
  (i : ℕ) (V : (ChartRing π)ˣ)
local notation "L" => R[T;T⁻¹]
local notation "C" => Units.map (RingHom.toMonoidHom (algebraMap R L))
local notation "T₁" => LaurentUnitPoints.pointUnit (AlgHom.id R L)
local notation "E" => Units.map (AlgHom.toMonoidHom' (leftLaurentMap π))

/-- The exact outgoing parameter includes every step of the coefficient recurrence. -/
theorem retainedFixedEdgeUnit_depth :
    retainedFixedEdgeUnit π q
        (retainedScaledCorrectionUnit π (retainedDepthScale q α i) V) =
      C (q ^ (i + 1) * α⁻¹) * T₁ * (E V)⁻¹ := by
  rw [retainedFixedEdgeUnit, retainedScaledCorrectionUnit_map]
  simp only [retainedDepthScale, map_mul, map_pow, map_inv, mul_inv_rev,
    inv_inv, inv_pow, pow_succ]
  ac_rfl

/-- The terminal comparison requires the reciprocal of the entire outgoing unit. -/
theorem retainedFixedEdgeUnit_depth_inv :
    (retainedFixedEdgeUnit π q
        (retainedScaledCorrectionUnit π (retainedDepthScale q α i) V))⁻¹ =
      C (α * (q⁻¹) ^ (i + 1)) * T₁⁻¹ * E V := by
  rw [retainedFixedEdgeUnit_depth]
  simp only [map_mul, map_pow, map_inv, mul_inv_rev, inv_inv, inv_pow]
  ac_rfl

/-- Starting with the original first node removes only the initial scalar. -/
theorem retainedFixedEdgeUnit_depth_one_inv :
    (retainedFixedEdgeUnit π q
        (retainedScaledCorrectionUnit π (retainedDepthScale q 1 i) V))⁻¹ =
      C ((q⁻¹) ^ (i + 1)) * T₁⁻¹ * E V := by
  simpa only [one_mul] using retainedFixedEdgeUnit_depth_inv π q 1 i V

end FLT.Mazur.WeierstrassModificationX
