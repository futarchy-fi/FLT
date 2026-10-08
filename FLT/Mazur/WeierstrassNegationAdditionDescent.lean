/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNegationAdditionPullback

/-!
# Affine inverse identity by descent along the addition cover

The ordinary members of the pulled-back cover are empty. The reciprocal members
send the point-negation pair to zero as scheme morphisms. Descent proves the
inverse identity on the entire affine curve chart.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Any common scheme over an ordinary domain and the negation section is empty. -/
theorem ordinaryNegation_commonScheme_isEmpty (b : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
    (g : X ⟶ chartScheme W 2)
    (h : f ≫ additionChartInclusion W (ordinaryIndex b) =
      g ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) : IsEmpty X := by
  let _ := negationAddition_ordinary_isEmpty W b
  exact Function.isEmpty ((negationAddition_isPullback W (ordinaryIndex b)).lift f g h)

/-- On the reciprocal tensor pullback, addition is the base-valued zero section. -/
theorem reciprocalNegation_pullback_zero (b : Bool) :
    Spec.map (CommRingCat.ofHom (negationAdditionFirst W (reciprocalIndex b)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
          integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (negationAdditionSecond W (reciprocalIndex b)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) ≫
          integralCurveZero W := by
  rw [← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((negationAdditionFirst W (reciprocalIndex b)).comp
      (reciprocalChartAddition W b)).toRingHom)) ≫ _ = _
  rw [negationAddition_reciprocal, ← Category.assoc, specAlgHom_structure]
  rw [integralCurveZero, ← Category.assoc, ← Spec.map_comp]
  rw [chartInfinityEvaluation_base]
  rfl

/-- The reciprocal identity holds over every common scheme, not only affine points. -/
theorem reciprocalNegation_commonScheme (b : Bool) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W (reciprocalIndex b)))
    (g : X ⟶ chartScheme W 2)
    (h : f ≫ additionChartInclusion W (reciprocalIndex b) =
      g ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) :
    f ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W b).toRingHom) ≫
        integralCurveChart W 1 =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) ≫
        integralCurveZero W := by
  have hp := negationAddition_isPullback W (reciprocalIndex b)
  have he := congrArg (fun t => hp.lift f g h ≫ t) (reciprocalNegation_pullback_zero W b)
  simpa only [← Category.assoc, hp.lift_fst, hp.lift_snd] using he

/-- Every addition domain sends the affine point-negation section to zero. -/
theorem additionNegation_commonScheme (i : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ chartScheme W 2)
    (h : f ≫ additionChartInclusion W i =
      g ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) :
    f ≫ additionCurveChart W i =
      g ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) ≫
        integralCurveZero W := by
  cases i
  · let _ := ordinaryNegation_commonScheme_isEmpty W false f g h
    exact isInitialOfIsEmpty.hom_ext _ _
  · let _ := ordinaryNegation_commonScheme_isEmpty W true f g h
    exact isInitialOfIsEmpty.hom_ext _ _
  · exact reciprocalNegation_commonScheme W false f g h
  · exact reciprocalNegation_commonScheme W true f g h

/-- The descended affine addition sends a point and its actual negation to zero. -/
theorem affineAdditionToCurve_negation (hΔ : IsUnit W.Δ) :
    Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom) ≫
        affineAdditionToCurve W hΔ =
      Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 2))) ≫
        integralCurveZero W := by
  let g := Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)
  let C := additionAffineOpenCover W hΔ
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : q ≫ additionChartInclusion W i = p ≫ g :=
    Scheme.Cover.pullbackHom_map C g i
  change p ≫ (g ≫ affineAdditionToCurve W hΔ) = _
  rw [← Category.assoc, ← hi, Category.assoc, additionCurveChart_glued]
  exact additionNegation_commonScheme W i q p hi

/-- Global addition has the right inverse identity on its entire affine input chart. -/
theorem integralCurveAddition_rightNegation_affine (hΔ : IsUnit W.Δ) :
    integralCurveChart W 2 ≫ integralCurveRightNegation W ≫ integralCurveAddition W hΔ =
      integralCurveChart W 2 ≫ integralCurveStructure W ≫ integralCurveZero W := by
  rw [← Category.assoc, integralCurveChart_rightNegation_affine, Category.assoc,
    integralCurveProductChart_addition]
  rw [integralInputAdditionToCurve_commonAffine W hΔ false false
    (Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) _ rfl]
  rw [affineAdditionToCurve_negation, ← Category.assoc, integralCurveChart_structure]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
