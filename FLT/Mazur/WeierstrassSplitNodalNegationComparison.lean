/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSplitNodalInversion
public import FLT.Mazur.WeierstrassSplitNodalTorus
public import FLT.Mazur.WeierstrassGlobalNegation

/-!
# The torus inverse agrees with the actual global cubic negation

The Laurent chart lies in the original negation neighborhood. Lifting its
coordinate map through that localization identifies the normalized formulas,
and hence the actual scheme morphisms, over arbitrary coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (a : Rˣ)

/-- The actual negation denominator is invertible everywhere on the Laurent chart. -/
theorem splitNodalNegationDen_isUnit :
    IsUnit (splitNodalChartToLaurent a (infinityNegationDen (splitNodalEquation a))) := by
  rw [splitNodalLaurent_negationDen]
  exact (LaurentPolynomial.isUnit_T 1).neg

/-- The torus chart lifts through the original localized infinity negation neighborhood. -/
def splitNodalNegationLift : InfinityNegationOpen (splitNodalEquation a) →ₐ[R] R[T;T⁻¹] :=
  IsLocalization.Away.liftAlgHom _ (splitNodalNegationDen_isUnit a)

/-- The lift restricts to the original explicit Laurent comparison. -/
theorem splitNodalNegationLift_restriction :
    (splitNodalNegationLift a).comp (infinityNegationRestriction (splitNodalEquation a)) =
      splitNodalChartToLaurent a := by
  apply AlgHom.ext
  intro x
  exact IsLocalization.Away.lift_eq _ (splitNodalNegationDen_isUnit a) x

/-- The normalization factor on the torus is the negative inverse Laurent coordinate. -/
theorem splitNodalNegationLift_inverse :
    splitNodalNegationLift a (infinityNegationInverse (splitNodalEquation a)) =
      -LaurentPolynomial.T (-1) := by
  have h := congrArg (splitNodalNegationLift a)
    (infinityNegationInverse_mul (splitNodalEquation a))
  rw [map_mul, map_one] at h
  have hr := DFunLike.congr_fun (splitNodalNegationLift_restriction a)
    (infinityNegationDen (splitNodalEquation a))
  change splitNodalNegationLift a (infinityNegationRestriction _ _) = _ at hr
  rw [hr, splitNodalLaurent_negationDen] at h
  apply (IsUnit.mul_left_inj (LaurentPolynomial.isUnit_T (R := R) 1).neg).mp
  rw [h, neg_mul_neg, ← LaurentPolynomial.T_add]
  rfl

/-- The actual localized negation law agrees with Laurent inversion on every coordinate. -/
theorem splitNodalNegationLift_chart :
    (splitNodalNegationLift a).comp (infinityNegationChart (splitNodalEquation a)) =
      LaurentPolynomial.invert.toAlgHom.comp (splitNodalChartToLaurent a) := by
  apply hom_ext
  intro i
  change splitNodalNegationLift a (infinityNegationChart _ _) = _
  rw [infinityNegationChart_coord, map_mul, splitNodalNegationLift_inverse]
  have hr := DFunLike.congr_fun (splitNodalNegationLift_restriction a)
    (chartNegationCoordinates (splitNodalEquation a) 1 i)
  change splitNodalNegationLift a (infinityNegationRestriction _ _) = _ at hr
  rw [hr]
  exact (splitNodalLaurent_negation_coord a i).symm

/-- The lifted torus point has exactly the original chart inclusion. -/
theorem splitNodalNegationLift_spec :
    Spec.map (CommRingCat.ofHom (splitNodalNegationLift a).toRingHom) ≫
      infinityNegationInclusion (splitNodalEquation a) = (splitNodalTorusIso a).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
    (splitNodalNegationLift_restriction a)

/-- Torus inversion agrees with the existing global regular negation on the actual cubic. -/
theorem splitNodalTorusToCurve_negation :
    Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.toAlgHom.toRingHom) ≫
        splitNodalTorusToCurve a =
      splitNodalTorusToCurve a ≫ integralCurveNegation (splitNodalEquation a) := by
  have h : Spec.map (CommRingCat.ofHom (splitNodalNegationLift a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (infinityNegationChart (splitNodalEquation a)).toRingHom) =
        Spec.map (CommRingCat.ofHom LaurentPolynomial.invert.toAlgHom.toRingHom) ≫
          (splitNodalTorusIso a).hom := by
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      ((splitNodalNegationLift a).comp (infinityNegationChart _)).toRingHom) = _
    rw [splitNodalNegationLift_chart]
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]
    rfl
  rw [splitNodalTorusToCurve, ← Category.assoc, ← h, Category.assoc,
    ← integralCurveChart_negation_infinity, ← Category.assoc,
    splitNodalNegationLift_spec, Category.assoc]

end FLT.Mazur.WeierstrassIntegralChart
