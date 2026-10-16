/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedSmoothing
public import FLT.Mazur.WeierstrassRetainedAdjacentFactors

/-!
# Coefficient scales for a single retained target smoothing

When the fixed quotient q is a unit, the incoming correction at the next
node is scaled by q⁻¹. Iterating this recurrence keeps the target smoothing
fixed while allowing the local root smoothing to change at every depth.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
variable {R : Type*} [CommRing R] (π : R)

/-- Multiply the full node correction by a coefficient unit. -/
def retainedScaledCorrectionUnit (α : Rˣ) (V : (ChartRing π)ˣ) : (ChartRing π)ˣ :=
  Units.map (algebraMap R (ChartRing π)).toMonoidHom α * V

/-- The coefficient scale at a retained depth, relative to its first node. -/
def retainedDepthScale (q α : Rˣ) (i : ℕ) : Rˣ := α * (q⁻¹) ^ i

/-- The first retained node keeps the prescribed initial scale. -/
@[simp] theorem retainedDepthScale_zero (q α : Rˣ) : retainedDepthScale q α 0 = α := by
  simp [retainedDepthScale]

/-- Consecutive incoming scales differ by precisely the inverse global quotient. -/
theorem retainedDepthScale_succ (q α : Rˣ) (i : ℕ) :
    retainedDepthScale q α (i + 1) = retainedDepthScale q α i * q⁻¹ := by
  simp only [retainedDepthScale, pow_succ, mul_assoc]

/-- Evaluation transports a scaled correction without changing its coefficient scale. -/
theorem retainedScaledCorrectionUnit_map (α : Rˣ) (V : (ChartRing π)ˣ)
    (e : ChartRing π →ₐ[R] R[T;T⁻¹]) :
    Units.map e.toMonoidHom (retainedScaledCorrectionUnit π α V) =
      Units.map (algebraMap R R[T;T⁻¹]).toMonoidHom α * Units.map e.toMonoidHom V := by
  apply Units.ext
  change e (algebraMap R _ (α : R) * (V : ChartRing π)) = _
  rw [map_mul, AlgHom.commutes]
  rfl

/-- The next entire edge correction is the previous one multiplied by q⁻¹. -/
theorem retainedScaledCorrectionUnit_adjacent (q α : Rˣ) (V V' : (ChartRing π)ˣ)
    (hV : Units.map (leftLaurentMap π).toMonoidHom V =
      Units.map (retainedPrecedingEvaluation π).toMonoidHom V') :
    Units.map (retainedPrecedingEvaluation π).toMonoidHom
        (retainedScaledCorrectionUnit π (α * q⁻¹) V') =
      Units.map (leftLaurentMap π).toMonoidHom (retainedScaledCorrectionUnit π α V) *
        Units.map (algebraMap R R[T;T⁻¹]).toMonoidHom q⁻¹ := by
  rw [retainedScaledCorrectionUnit_map, retainedScaledCorrectionUnit_map, hV, map_mul]
  exact mul_right_comm _ _ _

end FLT.Mazur.WeierstrassModificationX
