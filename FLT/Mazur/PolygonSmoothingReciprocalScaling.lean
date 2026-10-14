/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCoordinateIdeal

/-!
# Reciprocal scaling of the full arithmetic node

Scaling the two coordinates by reciprocal coefficient units preserves xy=t,
including the smoothing parameter and all nilpotents. It preserves the full
coordinate ideal, so it can act on the actual node neighborhoods and completion.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R] (t : R)

/-- Reciprocal branch scaling on the full smoothing ring over its original base. -/
def reciprocalScale (a : Rˣ) : ChartRing t →ₐ[R] ChartRing t :=
  evaluate t (algebraMap R _ a * leftCoordinate t)
    (algebraMap R _ ↑a⁻¹ * rightCoordinate t) (by
      rw [mul_mul_mul_comm, ← map_mul, Units.mul_inv, map_one, one_mul,
        coordinate_relation])

/-- The first branch has weight one. -/
@[simp] theorem reciprocalScale_left (a : Rˣ) :
    reciprocalScale t a (leftCoordinate t) = algebraMap R _ a * leftCoordinate t :=
  evaluate_left ..

/-- The second branch has weight minus one. -/
@[simp] theorem reciprocalScale_right (a : Rˣ) :
    reciprocalScale t a (rightCoordinate t) = algebraMap R _ ↑a⁻¹ * rightCoordinate t :=
  evaluate_right ..

/-- The unit parameter acts identically on the entire smoothing ring. -/
@[simp] theorem reciprocalScale_one : reciprocalScale t 1 = AlgHom.id R (ChartRing t) := by
  apply chartRing_hom_ext t <;> simp

/-- Multiplication of units gives composition on the full smoothing ring. -/
theorem reciprocalScale_mul (a b : Rˣ) :
    reciprocalScale t (a * b) = (reciprocalScale t a).comp (reciprocalScale t b) := by
  apply chartRing_hom_ext t <;> simp [mul_left_comm, mul_comm]

/-- Every coefficient-unit scaling is an automorphism of the arithmetic node. -/
def reciprocalScaleEquiv (a : Rˣ) : ChartRing t ≃ₐ[R] ChartRing t :=
  { reciprocalScale t a with
    invFun := reciprocalScale t a⁻¹
    left_inv := fun x ↦ by
      have hx := DFunLike.congr_fun (reciprocalScale_mul t a⁻¹ a) x
      simpa using hx.symm
    right_inv := fun x ↦ by
      have hx := DFunLike.congr_fun (reciprocalScale_mul t a a⁻¹) x
      simpa using hx.symm }

/-- Scaling maps the full coordinate ideal into itself. -/
theorem reciprocalScale_coordinateIdeal_le (a : Rˣ) :
    (coordinateIdeal t).map (reciprocalScale t a).toRingHom ≤ coordinateIdeal t := by
  rw [Ideal.map_le_iff_le_comap, coordinateIdeal, Ideal.span_le]
  intro x hx
  rcases hx with rfl | hx
  · change reciprocalScale t a (leftCoordinate t) ∈ coordinateIdeal t
    rw [reciprocalScale_left]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rcases hx with rfl
    change reciprocalScale t a (rightCoordinate t) ∈ coordinateIdeal t
    rw [reciprocalScale_right]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

/-- The full node ideal, rather than just its radical, is invariant. -/
theorem reciprocalScale_coordinateIdeal (a : Rˣ) :
    (coordinateIdeal t).map (reciprocalScale t a).toRingHom = coordinateIdeal t := by
  apply le_antisymm (reciprocalScale_coordinateIdeal_le t a)
  have hi := Ideal.map_mono (f := (reciprocalScale t a).toRingHom)
    (reciprocalScale_coordinateIdeal_le t a⁻¹)
  have hc : (reciprocalScale t a).toRingHom.comp
      (reciprocalScale t a⁻¹).toRingHom = RingHom.id (ChartRing t) := by
    change ((reciprocalScale t a).comp (reciprocalScale t a⁻¹)).toRingHom = _
    rw [← reciprocalScale_mul, mul_inv_cancel, reciprocalScale_one]
    rfl
  simpa only [Ideal.map_map, hc, Ideal.map_id] using hi

/-- Reciprocal scaling fixes the actual node evaluation over R/(t). -/
theorem coordinateZeroEvaluation_reciprocalScale (a : Rˣ) :
    (coordinateZeroEvaluation t).comp (reciprocalScale t a) = coordinateZeroEvaluation t := by
  apply chartRing_hom_ext t <;> simp [coordinateZeroEvaluation]

end FLT.Mazur.PolygonSmoothing
