/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalizationCoordinates

/-!
# Reverse coordinates for the affine normalization

The coordinate z=t/(t-1) is an involution on D(t-1). The other chart
has coordinate w=1-t⁻¹ and inverse t=1/(1-w), in every characteristic.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
universe u
namespace FLT.Mazur.OneGonAffineNormalizationCoordinates
open OneGonTransition OneGonAffineCover OneGonNormalizationCoordinates
variable (K : Type u) [Field K]

local instance : IsScalarTower K K[X] K[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    simp [LaurentPolynomial.algebraMap_eq_toLaurent]

theorem leftCoordinate_sub_one : leftCoordinate K - 1 = (↑(denominator K)⁻¹ : awayOne K) := by
  have h := Units.mul_inv (denominator K)
  simp only [denominator_val, map_sub, map_one] at h
  dsimp [leftCoordinate]
  linear_combination h

/-- The Möbius substitution on the larger open D(t-1). -/
def leftChange : awayOne K →ₐ[K] awayOne K :=
  IsLocalization.Away.liftAlgHom (X - 1 : K[X]) (f := aeval (leftCoordinate K))
    (by simpa only [map_sub, map_one, aeval_X, leftCoordinate_sub_one]
        using ((denominator K)⁻¹).isUnit)

@[simp]
theorem leftChange_X : leftChange K (algebraMap K[X] _ X) = leftCoordinate K := by
  simp [leftChange, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

theorem leftChange_denominator :
    Units.map (leftChange K).toMonoidHom (denominator K) = (denominator K)⁻¹ := by
  apply Units.ext
  simp [leftCoordinate_sub_one]

@[simp]
theorem leftChange_leftCoordinate : leftChange K (leftCoordinate K) = algebraMap K[X] _ X := by
  have hi := congrArg (fun v : (awayOne K)ˣ ↦ (↑v⁻¹ : awayOne K)) (leftChange_denominator K)
  change leftChange K (↑(denominator K)⁻¹ : awayOne K) = ↑(denominator K) at hi
  simp only [leftCoordinate, map_mul, leftChange_X, hi]
  simp only [mul_assoc, Units.inv_mul, mul_one]

/-- The inverse is the same Möbius substitution. -/
def leftEquiv : awayOne K ≃ₐ[K] awayOne K := by
  have h : (leftChange K).comp (leftChange K) = AlgHom.id K (awayOne K) := by
    apply IsLocalization.algHom_ext (Submonoid.powers (X - 1 : K[X]))
    ext
    exact (congrArg (leftChange K) (leftChange_X K)).trans (leftChange_leftCoordinate K)
  exact AlgEquiv.ofAlgHom (leftChange K) (leftChange K) h h

/-- Pullback of functions in w under w=1-t⁻¹. -/
def rightChange : awayOne K →ₐ[K] K[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom (X - 1 : K[X])
    (f := aeval (1 - LaurentPolynomial.T (-1)))
    (by simpa using (LaurentPolynomial.isUnit_T (R := K) (-1)).neg)

/-- Pullback under the inverse t=1/(1-w). -/
def rightInverse : K[T;T⁻¹] →ₐ[K] awayOne K :=
  IsLocalization.Away.liftAlgHom (X : K[X]) (f := aeval (rightCoordinate K))
    (by simp [rightCoordinate])

@[simp]
theorem rightChange_X : rightChange K (algebraMap K[X] _ X) =
    1 - LaurentPolynomial.T (-1) := by
  simp [rightChange, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]

@[simp]
theorem rightInverse_T : rightInverse K (LaurentPolynomial.T 1) = rightCoordinate K := by
  rw [← Polynomial.toLaurent_X, ← LaurentPolynomial.algebraMap_eq_toLaurent]
  unfold rightInverse
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact aeval_X _

@[simp]
theorem rightInverse_T_neg : rightInverse K (LaurentPolynomial.T (-1)) =
    -(algebraMap K[X] (awayOne K) X - 1) := by
  have h : rightInverse K (LaurentPolynomial.T (-1)) * rightCoordinate K = 1 := by
    rw [← rightInverse_T, ← map_mul, ← LaurentPolynomial.T_add]
    simp
  apply (IsUnit.mul_left_inj (((denominator K)⁻¹).isUnit.neg)).mp
  change _ * rightCoordinate K = _ * rightCoordinate K
  rw [h]
  rw [show algebraMap K[X] (awayOne K) X - 1 = (denominator K : awayOne K) by simp]
  simp only [rightCoordinate, neg_mul_neg, Units.mul_inv]

@[simp]
theorem rightChange_rightCoordinate :
    rightChange K (rightCoordinate K) = LaurentPolynomial.T 1 := by
  have h : rightChange K (rightCoordinate K) * (-LaurentPolynomial.T (-1)) = -1 := by
    rw [← show rightChange K (↑(denominator K) : awayOne K) =
      -LaurentPolynomial.T (-1) by simp, ← map_mul]
    simp only [rightCoordinate, neg_mul, Units.inv_mul, map_neg, map_one]
  apply (IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (R := K) (-1)).neg).mp
  rw [h, mul_neg, ← LaurentPolynomial.T_add]
  simp

/-- The second reverse coordinate identifies D(t) with D(w-1). -/
def rightEquiv : awayOne K ≃ₐ[K] K[T;T⁻¹] := by
  refine AlgEquiv.ofAlgHom (rightChange K) (rightInverse K) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers (X : K[X]))
    apply Polynomial.algHom_ext
    change rightChange K (rightInverse K (algebraMap K[X] K[T;T⁻¹] X)) =
      algebraMap K[X] K[T;T⁻¹] X
    rw [LaurentPolynomial.algebraMap_eq_toLaurent, Polynomial.toLaurent_X,
      rightInverse_T, rightChange_rightCoordinate]
  · apply IsLocalization.algHom_ext (Submonoid.powers (X - 1 : K[X]))
    ext
    change rightInverse K (rightChange K (algebraMap K[X] _ X)) = algebraMap K[X] _ X
    simp

/-- The first reverse coordinate as a scheme isomorphism. -/
def leftIso : Spec (.of (awayOne K)) ≅ Spec (.of (awayOne K)) :=
  Scheme.Spec.mapIso (leftEquiv K).toRingEquiv.toCommRingCatIso.op

/-- The second reverse coordinate as a scheme isomorphism. -/
def rightIso : ProjectiveLine.overlap K ≅ Spec (.of (awayOne K)) :=
  Scheme.Spec.mapIso (rightEquiv K).toRingEquiv.toCommRingCatIso.op

/-- z=t/(t-1) on D(t-1). -/
def leftChart := (leftIso K).hom ≫ openOne K

/-- w=1-t⁻¹ on D(t). -/
def rightChart := (rightIso K).hom ≫ openOne K

instance : IsOpenImmersion (leftChart K) := by unfold leftChart; infer_instance
instance : IsOpenImmersion (rightChart K) := by unfold rightChart; infer_instance

theorem leftChart_eq : leftChart K =
    Spec.map (CommRingCat.ofHom (aeval (leftCoordinate K)).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (leftChange K).toRingHom.comp (algebraMap K[X] _) = _
  apply RingHom.ext
  intro p
  change leftChange K (algebraMap K[X] _ p) = aeval (leftCoordinate K) p
  unfold leftChange
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

theorem rightChart_eq : rightChart K =
    Spec.map (CommRingCat.ofHom (aeval (1 - LaurentPolynomial.T (-1) : K[T;T⁻¹])).toRingHom) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  change (rightChange K).toRingHom.comp (algebraMap K[X] _) = _
  apply RingHom.ext
  intro p
  change rightChange K (algebraMap K[X] _ p) = aeval _ p
  unfold rightChange
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

@[reassoc]
theorem toOne_leftChart : toOne K ≫ leftChart K =
    toTorus K ≫ ProjectiveLine.overlapLeft K := by
  rw [leftChart_eq, toTorus_eq_specMap]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change restrictOne K (aeval _ (C r)) = overlapMap K (Polynomial.toLaurent (C r))
    rw [aeval_C, Polynomial.toLaurent_C]
    change restrictOne K (algebraMap K[X] (awayOne K) (C r)) =
      transition K (torusRestriction K (LaurentPolynomial.C r))
    rw [restrictOne_algebraMap, torusRestriction_C, AlgHom.commutes]
    rfl
  · change restrictOne K (aeval _ X) = overlapMap K (Polynomial.toLaurent X)
    simp

@[reassoc]
theorem toLaurent_rightChart : toLaurent K ≫ rightChart K =
    toTorus K ≫ ProjectiveLine.overlapRight K := by
  rw [rightChart_eq, toTorus_eq_specMap, ProjectiveLine.overlapRight,
    ProjectiveLine.inversion_hom]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro r
    change torusRestriction K (aeval _ (C r)) =
      overlapMap K (LaurentPolynomial.invert (Polynomial.toLaurent (C r)))
    simp
  · change torusRestriction K (aeval _ X) =
      overlapMap K (LaurentPolynomial.invert (Polynomial.toLaurent X))
    simp only [aeval_X, map_sub, map_one, torusRestriction_T_neg,
      Polynomial.toLaurent_X, LaurentPolynomial.invert_T]
    have h : overlapMap K (LaurentPolynomial.T (-1)) * (mobius K : puncture K) = 1 := by
      rw [← overlapMap_T, ← map_mul, ← LaurentPolynomial.T_add]
      simp
    apply (IsUnit.mul_left_inj (mobius K).isUnit).mp
    rw [h]
    change (1 - (↑(coordinate K)⁻¹ : puncture K)) *
      ((coordinate K : puncture K) * ↑(difference K)⁻¹) = 1
    rw [← mul_assoc, sub_mul, one_mul, Units.inv_mul, ← difference_val, Units.mul_inv]

end FLT.Mazur.OneGonAffineNormalizationCoordinates
