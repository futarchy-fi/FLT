/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOriginalSmoothTangentPresentation
public import FLT.Mazur.WeierstrassDividedTangentRefinementComparison

/-!
# Divided tangents agree with the original smooth action on affine refinements

An originally smooth first input supplies both the ordinary presentation and
regularity of the scale. The resulting output equality concerns the actual
original action; neither an output identity nor a denominator is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S B : Type u} [CommRing R] [CommRing S] [CommRing B]
  [Algebra R S] [Algebra R B] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (e : DividedTangentRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6

variable (ha : Set.range (Spec.map (CommRingCat.ofHom
    (((e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp a)).toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆ WeierstrassIntegralChart.integralSmoothOpen W)

include ha in
/-- The constructed ordinary presentation has exactly the divided tangent output. -/
theorem dividedTangentRefinement_originalPresentation :
    e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6) =
      (dividedOriginalSmoothTangentPairPresentation W s b3 b4 b6 h3 h4 h6 a' c' ha
        (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e)).comp
          (WeierstrassIntegralChart.ordinaryChartAddition W true) := by
  exact dividedTangentRefinement_output W s b3 b4 b6 a c h3 h4 h6 e true _
    (dividedOriginalSmoothTangentPairPresentation_left ..)
    (dividedOriginalSmoothTangentPairPresentation_right ..)
    (dividedOriginalSmooth_scale_isUnit W s b3 b4 b6 h3 h4 h6 a' ha).isRegular

variable (p : Spec (.of B) ⟶ (WeierstrassIntegralChart.integralSmoothOpen W).toScheme)
  (hp : Spec.map (CommRingCat.ofHom
    (((e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp a)).toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6 =
        p ≫ (WeierstrassIntegralChart.integralSmoothOpen W).ι)
  (hb : p ≫ WeierstrassIntegralChart.integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom
      (((e.comp (IsScalarTower.toAlgHom R S
      (DividedTangentRing W s b3 b4 b6 a c))).comp c)).toRingHom) ≫
        toCurve W s b3 b4 b6 h3 h4 h6) ≫
          WeierstrassIntegralChart.integralCurveStructure W)

include hp in
/-- The actual divided formula agrees with the genuine original left smooth action. -/
theorem dividedTangentRefinement_originalAction :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      WeierstrassIntegralChart.leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom (c').toRingHom) ≫
          toCurve W s b3 b4 b6 h3 h4 h6) hb := by
  have ha' : Set.range (Spec.map (CommRingCat.ofHom (a').toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆
        WeierstrassIntegralChart.integralSmoothOpen W := by
    rw [hp]
    rintro _ ⟨z, rfl⟩
    exact (p z).property
  have hl : Spec.map (CommRingCat.ofHom ((a').comp orig).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        p ≫ (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
    rw [toCurve, ← Category.assoc, ← Spec.map_comp] at hp
    exact hp
  have hr : Spec.map (CommRingCat.ofHom ((c').comp orig).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        Spec.map (CommRingCat.ofHom (c').toRingHom) ≫
          toCurve W s b3 b4 b6 h3 h4 h6 := by
    rw [toCurve, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hb' := hb
  rw [← hr] at hb'
  have he := WeierstrassIntegralChart.ordinaryPairPresentation_addition W
    ((a').comp orig) ((c').comp orig) true
    (dividedOriginalSmoothTangentPair_denominator W s b3 b4 b6 h3 h4 h6 a' c' ha'
      (dividedTangentRefinement_denominator_isUnit W s b3 b4 b6 a c e)) p hl hb'
  simp only [hr] at he
  rw [dividedTangentToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (e.comp (dividedTangentOutput W s b3 b4 b6 a c h3 h4 h6)).toRingHom) ≫ _ = _
  rw [dividedTangentRefinement_originalPresentation W s b3 b4 b6 a c h3 h4 h6 e ha']
  exact he

end FLT.Mazur.WeierstrassDilatation
