/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLocalAdditionCurveComparison

/-!
# Transported chart comparisons without a discriminant assumption

The actual tensor-ring domains already support the output overlap maps over
arbitrary coefficient rings. Their curve-valued comparisons therefore do not
need the good-reduction cover used by the earlier global construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Transported affine and polynomial outputs coincide over every coefficient equation. -/
theorem transportedPolynomial_curve_eq_arbitrary (j k : Fin 3) (i : AdditionChartIndex)
    (t : Fin 3) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (TransportedAdditionRing W j k i)))
    (g : X ⟶ Spec (.of (AdditionOutputOpen W j k t)))
    (h : f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionInput W j k i).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)) :
    f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionAffine W j k i).toRingHom) ≫
        additionCurveChart W i =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) ≫
        integralCurveChart W t := by
  have he := integralCurve_output_eq W t (additionChartOutput i) _ _
    (transportedPolynomialCommonOutput W j k i t f g h)
    (transportedPolynomialCommonOutput_polynomial W j k i t f g h)
    (transportedPolynomialCommonOutput_affine W j k i t f g h)
  simpa only [Category.assoc, additionCurveChart] using he.symm

/-- Transported affine and infinity outputs coincide on their full common domain. -/
theorem transportedInfinity_curve_eq_arbitrary (i : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (TransportedAdditionRing W 1 1 i)))
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionInput W 1 1 i).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom)) :
    f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionAffine W 1 1 i).toRingHom) ≫
        additionCurveChart W i =
      g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  have he := integralCurve_output_eq W (additionChartOutput i) 1 _ _
    (infinityTransportedCommonOutput W i f g h)
    (infinityTransportedCommonOutput_affine W i f g h)
    (infinityTransportedCommonOutput_infinity W i f g h)
  simpa only [Category.assoc, additionCurveChart, infinityAdditionSpec] using he

end FLT.Mazur.WeierstrassIntegralChart
