/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingMarkedSection
public import FLT.Mazur.PolygonSmoothingScalingNaturality

/-!
# The actual principal ideal of an arithmetic unit marking

In the full xy=t chart the marking (a,t/a) has ideal (x-a). This identifies
the scheme-theoretic ideal, including all coefficient nilpotents, rather than
only its closed support. It supplies the local equation for pole-degree bounds.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] (t : R) (a : Rˣ)

/-- The original outgoing marking has the literal equation x-a in the arithmetic chart. -/
def markedCoordinateIdeal : Ideal (ChartRing t) :=
  Ideal.span {leftCoordinate t - algebraMap R (ChartRing t) (a : R)}

/-- The original marking evaluation annihilates this full principal ideal. -/
theorem markedCoordinateIdeal_le_ker :
    markedCoordinateIdeal t a ≤ RingHom.ker (markedEvaluation t a).toRingHom := by
  rw [markedCoordinateIdeal, Ideal.span_le, Set.singleton_subset_iff]
  change markedEvaluation t a (leftCoordinate t - algebraMap R (ChartRing t) (a : R)) = 0
  simp only [map_sub, markedEvaluation_left, AlgHom.commutes,
    Algebra.algebraMap_self, RingHom.id_apply, sub_self]

/-- Quotienting by x-a retains exactly the original marked value of every function. -/
theorem markedCoordinateIdeal_quotient_evaluation (z : ChartRing t) :
    Ideal.Quotient.mk (markedCoordinateIdeal t a) z =
      Ideal.Quotient.mk (markedCoordinateIdeal t a)
        (algebraMap R (ChartRing t) (markedEvaluation t a z)) := by
  let I := markedCoordinateIdeal t a
  let Q := ChartRing t ⧸ I
  let _ : CommRing Q := inferInstanceAs (CommRing (ChartRing t ⧸ I))
  let f : ChartRing t →+* Q := Ideal.Quotient.mk I
  let c : R →+* Q := f.comp (algebraMap R (ChartRing t))
  have hx : f (leftCoordinate t) = c (a : R) := by
    apply sub_eq_zero.mp
    change Ideal.Quotient.mk I
      (leftCoordinate t - algebraMap R (ChartRing t) (a : R)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hr : c (a : R) * f (rightCoordinate t) = c t := by
    rw [← hx, ← map_mul, coordinate_relation]
    rfl
  have hy : f (rightCoordinate t) = c (t * ↑a⁻¹) := by
    calc
      _ = c (↑a⁻¹ : R) * (c (a : R) * f (rightCoordinate t)) := by
        rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
      _ = _ := by rw [hr, map_mul, mul_comm]
  have he : f = c.comp (markedEvaluation t a).toRingHom := by
    apply chartRing_ringHom_ext (S := Q) t
    · intro r
      change c r = c (markedEvaluation t a (algebraMap R (ChartRing t) r))
      rw [AlgHom.commutes]
      rfl
    · change f (leftCoordinate t) = c (markedEvaluation t a (leftCoordinate t))
      rw [markedEvaluation_left]
      exact hx
    · change f (rightCoordinate t) = c (markedEvaluation t a (rightCoordinate t))
      rw [markedEvaluation_right]
      exact hy
  exact DFunLike.congr_fun he z

/-- The principal equation is the actual scheme-theoretic marking kernel. -/
theorem markedEvaluation_ker_eq :
    RingHom.ker (markedEvaluation t a).toRingHom = markedCoordinateIdeal t a := by
  apply le_antisymm _ (markedCoordinateIdeal_le_ker t a)
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [markedCoordinateIdeal_quotient_evaluation]
  change markedEvaluation t a z = 0 at hz
  rw [hz, map_zero, map_zero]

/-- At the original unit-one marking the exact ideal is (x-1), even over a thickened base. -/
theorem markedEvaluation_one_ker :
    RingHom.ker (markedEvaluation t 1).toRingHom = Ideal.span {leftCoordinate t - 1} := by
  rw [markedEvaluation_ker_eq, markedCoordinateIdeal]
  simp only [Units.val_one, map_one]

end FLT.Mazur.PolygonSmoothing
