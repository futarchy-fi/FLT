/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonAffineCover

/-!
# Coordinates of the one-gon normalization

On the two standard projective charts the pinched coordinate is respectively
z/(z-1) and 1/(1-w). Both are defined away from one, and have compatible
restrictions to the existing puncture.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial

universe u

namespace FLT.Mazur.OneGonNormalizationCoordinates

open OneGonTransition OneGonAffineCover PolygonNodePresentation

variable (K : Type u) [Field K]

/-- The invertible difference from one on D(X-1). -/
def denominator : (awayOne K)ˣ := (IsLocalization.Away.algebraMap_isUnit (X - 1 : K[X])).unit

@[simp]
theorem denominator_val : (denominator K : awayOne K) = algebraMap K[X] _ (X - 1) :=
  IsUnit.unit_spec _

/-- The left projective chart's pinched coordinate. -/
def leftCoordinate : awayOne K := algebraMap K[X] _ X * ↑(denominator K)⁻¹

/-- The right projective chart's pinched coordinate. -/
def rightCoordinate : awayOne K := -(↑(denominator K)⁻¹ : awayOne K)

theorem restrict_denominator :
    Units.map (restrictOne K) (denominator K) = difference K := by
  apply Units.ext
  simp [difference_val]

@[simp]
theorem restrict_leftCoordinate : restrictOne K (leftCoordinate K) = (mobius K : puncture K) := by
  have hi := congrArg (fun v : (puncture K)ˣ ↦ (↑v⁻¹ : puncture K)) (restrict_denominator K)
  simpa [leftCoordinate, mobius] using congrArg
    (fun v : puncture K ↦ algebraMap K[X] (puncture K) X * v) hi

@[simp]
theorem restrict_rightCoordinate : restrictOne K (rightCoordinate K) =
    -(↑(difference K)⁻¹ : puncture K) := by
  have hi := congrArg (fun v : (puncture K)ˣ ↦ (↑v⁻¹ : puncture K)) (restrict_denominator K)
  simpa [rightCoordinate] using congrArg Neg.neg hi

/-- Coordinate change on the puncture for the right projective chart. -/
def rightTransition : puncture K →ₐ[K] puncture K :=
  IsLocalization.Away.liftAlgHom (X * (X - 1) : K[X])
    (f := aeval (-(↑(difference K)⁻¹ : puncture K)))
    (by
      simp only [map_mul, map_sub, map_one, aeval_X]
      have hd : -(↑(difference K)⁻¹ : puncture K) - 1 = -(mobius K : puncture K) := by
        have := mobius_sub_one K
        linear_combination this
      rw [hd]
      exact ((difference K)⁻¹).isUnit.neg.mul (mobius K).isUnit.neg)

theorem rightTransition_coordinate :
    rightTransition K (coordinate K : puncture K) = -(↑(difference K)⁻¹ : puncture K) := by
  simp [rightTransition, IsLocalization.Away.liftAlgHom_apply]

theorem rightTransition_difference :
    rightTransition K (difference K : puncture K) = -(mobius K : puncture K) := by
  rw [difference_val, map_sub, map_one, rightTransition_coordinate]
  have := mobius_sub_one K
  linear_combination this

@[simp]
theorem rightTransition_mobius :
    rightTransition K (mobius K : puncture K) = (↑(coordinate K)⁻¹ : puncture K) := by
  have hd : Units.map (rightTransition K).toMonoidHom (difference K) = -(mobius K) := by
    apply Units.ext
    exact rightTransition_difference K
  have hi := congrArg (fun v : (puncture K)ˣ ↦ (↑v⁻¹ : puncture K)) hd
  change rightTransition K ((coordinate K : puncture K) * ↑(difference K)⁻¹) = _
  rw [map_mul, rightTransition_coordinate]
  rw [show rightTransition K (↑(difference K)⁻¹ : puncture K) = ↑(-(mobius K))⁻¹ from hi]
  simp [mobius, -difference_val, -coordinate_val, ← mul_assoc]

/-- The left local normalization map into the actual equalizer chart. -/
def leftPatch : Spec (.of (awayOne K)) ⟶ OneGonGluing.nodeChart K :=
  Spec.map (CommRingCat.ofHom
    ((aeval (leftCoordinate K)).toRingHom.comp (B (R := K)).val.toRingHom))

/-- The right local normalization map into the same equalizer chart. -/
def rightPatch : Spec (.of (awayOne K)) ⟶ OneGonGluing.nodeChart K :=
  Spec.map (CommRingCat.ofHom
    ((aeval (rightCoordinate K)).toRingHom.comp (B (R := K)).val.toRingHom))

/-- The right coordinate change as a scheme map of punctures. -/
def rightTransitionSpec : Spec (.of (puncture K)) ⟶ Spec (.of (puncture K)) :=
  Spec.map (CommRingCat.ofHom (rightTransition K).toRingHom)

@[reassoc]
theorem toOne_leftPatch :
    toOne K ≫ leftPatch K = (transitionSpecIso K).hom ≫ bPuncture K := by
  have he : (restrictOne K).comp (aeval (leftCoordinate K)).toRingHom =
      (transition K).toRingHom.comp (algebraMap K[X] (puncture K)) := by
    apply Polynomial.ringHom_ext
    · intro r
      change restrictOne K (aeval _ (C r)) = _
      rw [aeval_C]
      change restrictOne K (algebraMap K[X] (awayOne K) (C r)) = _
      rw [restrictOne_algebraMap]
      exact ((transition K).commutes r).symm
    · change restrictOne K (aeval _ X) = transition K (coordinate K : puncture K)
      rw [aeval_X, transition_coordinate, restrict_leftCoordinate]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun f : K[X] →+* puncture K ↦ f.comp (B (R := K)).val.toRingHom) he

@[reassoc]
theorem toOne_rightPatch :
    toOne K ≫ rightPatch K = rightTransitionSpec K ≫ bPuncture K := by
  have he : (restrictOne K).comp (aeval (rightCoordinate K)).toRingHom =
      (rightTransition K).toRingHom.comp (algebraMap K[X] (puncture K)) := by
    apply Polynomial.ringHom_ext
    · intro r
      change restrictOne K (aeval _ (C r)) = _
      rw [aeval_C]
      change restrictOne K (algebraMap K[X] (awayOne K) (C r)) = _
      rw [restrictOne_algebraMap]
      exact ((rightTransition K).commutes r).symm
    · change restrictOne K (aeval _ X) = rightTransition K (coordinate K : puncture K)
      rw [aeval_X, rightTransition_coordinate, restrict_rightCoordinate]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg (fun f : K[X] →+* puncture K ↦ f.comp (B (R := K)).val.toRingHom) he

@[reassoc]
theorem transition_toTorus :
    (transitionSpecIso K).hom ≫ toTorus K = toLaurent K := by
  rw [toTorus_eq_specMap]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext fun p ↦ transition_involutive K (torusRestriction K p)

@[simp]
theorem torusRestriction_T_neg : torusRestriction K (LaurentPolynomial.T (-1)) =
    (↑(coordinate K)⁻¹ : puncture K) := by
  calc
    _ = torusRestriction K (LaurentPolynomial.T (-1)) *
        ((coordinate K : puncture K) * ↑(coordinate K)⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = _ := by
      rw [← mul_assoc, ← torusRestriction_T, ← map_mul, ← LaurentPolynomial.T_add]
      norm_num

@[reassoc]
theorem rightTransition_toTorus :
    rightTransitionSpec K ≫ toTorus K = toLaurent K ≫ (ProjectiveLine.inversion K).hom := by
  rw [toTorus_eq_specMap, ProjectiveLine.inversion_hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : K[X]))
  apply Polynomial.ringHom_ext
  · intro r
    change rightTransition K (overlapMap K (Polynomial.toLaurent (C r))) =
      torusRestriction K (LaurentPolynomial.invert (Polynomial.toLaurent (C r)))
    simp
  · change rightTransition K (overlapMap K (Polynomial.toLaurent X)) =
      torusRestriction K (LaurentPolynomial.invert (Polynomial.toLaurent X))
    simp

end FLT.Mazur.OneGonNormalizationCoordinates
