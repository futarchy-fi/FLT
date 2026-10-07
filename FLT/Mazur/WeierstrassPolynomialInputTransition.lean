/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInputPolynomialScaling
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Equality of polynomial addition across input-chart transitions

Invert one output coordinate on the simultaneous input overlap. Homogeneous
scaling gives maps from both polynomial addition domains to this same ring,
and their normalized addition maps are equal there.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k j' k' t : Fin 3)

/-- The polynomial output open inside the simultaneous input overlap. -/
abbrev InputPolynomialOpen := Localization.Away
  (productOverlapRestriction W j k j' k' (chartProductAdditionCoordinates W j k t))

/-- Restriction of the input overlap to this output open. -/
def inputPolynomialRestriction : ProductOverlap W j k j' k' →ₐ[R]
    InputPolynomialOpen W j k j' k' t :=
  IsScalarTower.toAlgHom R _ _

/-- The chosen output coordinate is a unit in the original input presentation. -/
theorem inputPolynomial_isUnit : IsUnit
    ((inputPolynomialRestriction W j k j' k' t).comp (productOverlapRestriction W j k j' k')
      (chartProductAdditionCoordinates W j k t)) :=
  IsLocalization.Away.algebraMap_isUnit
    (productOverlapRestriction W j k j' k' (chartProductAdditionCoordinates W j k t))
    (S := InputPolynomialOpen W j k j' k' t)

/-- The same output coordinate is a unit in the changed input presentation. -/
theorem inputPolynomialOther_isUnit : IsUnit
    ((inputPolynomialRestriction W j k j' k' t).comp (productOverlapOther W j k j' k')
      (chartProductAdditionCoordinates W j' k' t)) := by
  change IsUnit (inputPolynomialRestriction W j k j' k' t
    (productOverlapOther W j k j' k' (chartProductAdditionCoordinates W j' k' t)))
  rw [productOverlap_addition_scaled, map_mul]
  exact ((productOverlapAdditionScale_isUnit W j k j' k').map
    (inputPolynomialRestriction W j k j' k' t)).mul (inputPolynomial_isUnit W j k j' k' t)

/-- The original polynomial addition domain restricts to the overlap output open. -/
def inputPolynomialOriginal : AdditionOutputOpen W j k t →ₐ[R]
    InputPolynomialOpen W j k j' k' t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j k t)
    (inputPolynomial_isUnit W j k j' k' t)

/-- The changed polynomial addition domain restricts to the same overlap output open. -/
def inputPolynomialOther : AdditionOutputOpen W j' k' t →ₐ[R]
    InputPolynomialOpen W j k j' k' t :=
  IsLocalization.Away.liftAlgHom (chartProductAdditionCoordinates W j' k' t)
    (inputPolynomialOther_isUnit W j k j' k' t)

/-- Restriction from the original polynomial domain retains its input functions. -/
@[simp] theorem inputPolynomialOriginal_restriction (a : ChartProduct W j k) :
    inputPolynomialOriginal W j k j' k' t (additionOutputRestriction W j k t a) =
      inputPolynomialRestriction W j k j' k' t (productOverlapRestriction W j k j' k' a) :=
  IsLocalization.Away.lift_eq _ (inputPolynomial_isUnit W j k j' k' t) a

/-- Restriction from the changed polynomial domain retains the normalized input functions. -/
@[simp] theorem inputPolynomialOther_restriction (a : ChartProduct W j' k') :
    inputPolynomialOther W j k j' k' t (additionOutputRestriction W j' k' t a) =
      inputPolynomialRestriction W j k j' k' t (productOverlapOther W j k j' k' a) :=
  IsLocalization.Away.lift_eq _ (inputPolynomialOther_isUnit W j k j' k' t) a

/-- The two normalized polynomial addition laws agree across both input-chart changes. -/
theorem inputPolynomialAddition_compatibility :
    (inputPolynomialOther W j k j' k' t).comp (projectiveAdditionChart W j' k' t) =
      (inputPolynomialOriginal W j k j' k' t).comp (projectiveAdditionChart W j k t) := by
  apply projectiveAdditionChart_comp_eq
  intro i
  have hi := congrArg (inputPolynomialOriginal W j k j' k' t)
    (projectiveAdditionChart_mul W j k t i)
  simp only [map_mul, inputPolynomialOriginal_restriction] at hi
  simp only [AlgHom.comp_apply, inputPolynomialOther_restriction,
    productOverlap_addition_scaled, map_mul]
  linear_combination
    inputPolynomialRestriction W j k j' k' t (productOverlapAdditionScale W j k j' k') * hi

open AlgebraicGeometry CategoryTheory

/-- The localized input overlap is the scheme intersection with the original output open. -/
theorem inputPolynomial_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (inputPolynomialRestriction W j k j' k' t).toRingHom))
      (Spec.map (CommRingCat.ofHom (inputPolynomialOriginal W j k j' k' t).toRingHom))
      (Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k j' k').toRingHom))
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)) := by
  have : IsLocalization
      ((Submonoid.powers (chartProductAdditionCoordinates W j k t)).map
        (productOverlapRestriction W j k j' k').toRingHom)
      (InputPolynomialOpen W j k j' k' t) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization
    (productOverlapRestriction W j k j' k').toRingHom
    (inputPolynomialOriginal W j k j' k' t).toRingHom
    (RingHom.ext (inputPolynomialOriginal_restriction W j k j' k' t))
    (Submonoid.powers (chartProductAdditionCoordinates W j k t))

/-- Polynomial addition agrees as a scheme map across the actual input overlap. -/
theorem inputPolynomialAddition_spec :
    Spec.map (CommRingCat.ofHom (inputPolynomialOther W j k j' k' t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j' k' t).toRingHom) =
      Spec.map (CommRingCat.ofHom (inputPolynomialOriginal W j k j' k' t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (inputPolynomialAddition_compatibility W j k j' k' t)

end FLT.Mazur.WeierstrassIntegralChart
