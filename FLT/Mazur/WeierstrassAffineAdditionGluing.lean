/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveMorphisms
public import FLT.Mazur.WeierstrassMixedIntersectionScheme

/-!
# Gluing affine-input addition into the integral projective cubic

The four regular affine-input laws have a common global target. Their existing
ordinary, reciprocal and mixed comparisons imply descent to a single morphism
on the entire affine input product when the discriminant is a unit.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Each of the four local laws viewed in the glued projective cubic. -/
def additionCurveChart (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ integralCurve W :=
  additionChartSpec W i ≫ integralCurveChart W (additionChartOutput i)

/-- The mixed comparison identifies global outputs on any common scheme. -/
theorem mixedAddition_curve_eq (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ Spec (additionChartRing W (reciprocalIndex c)))
    (hfg : f ≫ additionChartInclusion W (ordinaryIndex b) =
      g ≫ additionChartInclusion W (reciprocalIndex c)) :
    (f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom)) ≫
        integralCurveChart W 2 =
      (g ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom)) ≫
        integralCurveChart W 1 := by
  exact (integralCurve_output_eq W 1 2 _ _ (mixedCommonOutput W b c f g hfg)
    (mixedCommonOutput_reciprocal W b c f g hfg)
    (mixedCommonOutput_ordinary W b c f g hfg)).symm

/-- All four affine-input laws agree as curve-valued maps on common domains. -/
theorem additionCurveChart_commonScheme (i j : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ Spec (additionChartRing W j))
    (hfg : f ≫ additionChartInclusion W i = g ≫ additionChartInclusion W j) :
    f ≫ additionCurveChart W i = g ≫ additionCurveChart W j := by
  cases i <;> cases j
  · have he : f = g := (cancel_mono (additionChartInclusion W _)).mp hfg
    exact congrArg (fun t => t ≫ additionCurveChart W _) he
  · simpa only [additionCurveChart, additionChartOutput, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2) (ordinaryAddition_commonScheme W f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_curve_eq W false false f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_curve_eq W false true f g hfg
  · simpa only [additionCurveChart, additionChartOutput, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2)
        (ordinaryAddition_commonScheme W g f hfg.symm).symm
  · have he : f = g := (cancel_mono (additionChartInclusion W _)).mp hfg
    exact congrArg (fun t => t ≫ additionCurveChart W _) he
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_curve_eq W true false f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_curve_eq W true true f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_curve_eq W false false g f hfg.symm).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_curve_eq W true false g f hfg.symm).symm
  · have he : f = g := (cancel_mono (additionChartInclusion W _)).mp hfg
    exact congrArg (fun t => t ≫ additionCurveChart W _) he
  · simpa only [additionCurveChart, additionChartOutput, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1) (reciprocalAddition_commonScheme W f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_curve_eq W false true g f hfg.symm).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_curve_eq W true true g f hfg.symm).symm
  · simpa only [additionCurveChart, additionChartOutput, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1)
        (reciprocalAddition_commonScheme W g f hfg.symm).symm
  · have he : f = g := (cancel_mono (additionChartInclusion W _)).mp hfg
    exact congrArg (fun t => t ≫ additionCurveChart W _) he

/-- A regular addition morphism for all affine input pairs in good reduction. -/
def affineAdditionToCurve (hΔ : IsUnit W.Δ) :
    Spec (.of (AffineProduct W)) ⟶ integralCurve W :=
  (additionAffineOpenCover W hΔ).glueMorphisms (additionCurveChart W)
    (fun i j => additionCurveChart_commonScheme W i j _ _ pullback.condition)

/-- The glued morphism retains each of the original four formulas. -/
theorem additionCurveChart_glued (hΔ : IsUnit W.Δ) (i : AdditionChartIndex) :
    additionChartInclusion W i ≫ affineAdditionToCurve W hΔ = additionCurveChart W i :=
  (additionAffineOpenCover W hΔ).ι_glueMorphisms _ _ i

/-- Transported affine local laws are restrictions of the same glued morphism. -/
theorem affineOverlapAdditionSpec_glued (hΔ : IsUnit W.Δ) (j k : Fin 3)
    (i : AdditionChartIndex) :
    (affineOverlapAdditionCover W j k hΔ).f i ≫ affineInputOverlapMap W j k ≫
        affineAdditionToCurve W hΔ =
      affineOverlapAdditionSpec W j k hΔ i ≫ integralCurveChart W (additionChartOutput i) := by
  rw [← Category.assoc, ← affineOverlapAdditionProjection_inputs, Category.assoc,
    additionCurveChart_glued]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
