/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRightSmoothReciprocalPresentation
public import FLT.Mazur.WeierstrassReciprocalPresentationAction

/-!
# Divided reciprocals agree with the original smooth action of the right input

An originally smooth right input supplies the original reciprocal presentation.
The resulting normalized output is the actual original action, including at
infinity; no denominator or output identity is assumed.
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
  (e : DividedReciprocalOutputRing W s b3 b4 b6 a c →ₐ[R] B)
local notation "T" => DividedReciprocalRing W s b3 b4 b6 a c
local notation "O" => DividedReciprocalOutputRing W s b3 b4 b6 a c
local notation "j" => (IsScalarTower.toAlgHom R T O).comp (IsScalarTower.toAlgHom R S T)
local notation "a'" => (e.comp j).comp a
local notation "c'" => (e.comp j).comp c
local notation "orig" => fromOriginal W s b3 b4 b6 h3 h4 h6

variable (p : Spec (.of B) ⟶ (WeierstrassIntegralChart.integralSmoothOpen W).toScheme)
  (hp : Spec.map (CommRingCat.ofHom
    (((e.comp ((IsScalarTower.toAlgHom R
      (DividedReciprocalRing W s b3 b4 b6 a c)
      (DividedReciprocalOutputRing W s b3 b4 b6 a c)).comp
        (IsScalarTower.toAlgHom R S
          (DividedReciprocalRing W s b3 b4 b6 a c)))).comp c)).toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6 =
        p ≫ (WeierstrassIntegralChart.integralSmoothOpen W).ι)
  (hb : p ≫ WeierstrassIntegralChart.integralSmoothStructure W =
    (Spec.map (CommRingCat.ofHom
      (((e.comp ((IsScalarTower.toAlgHom R
      (DividedReciprocalRing W s b3 b4 b6 a c)
      (DividedReciprocalOutputRing W s b3 b4 b6 a c)).comp
        (IsScalarTower.toAlgHom R S
          (DividedReciprocalRing W s b3 b4 b6 a c)))).comp a)).toRingHom) ≫
        toCurve W s b3 b4 b6 h3 h4 h6) ≫
          WeierstrassIntegralChart.integralCurveStructure W)

include hp in
/-- The actual divided formula agrees with the genuine original smooth action of the right input. -/
theorem dividedReciprocalRefinement_rightOriginalAction :
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        dividedReciprocalToCurve W s b3 b4 b6 a c h3 h4 h6 =
      WeierstrassIntegralChart.leftSmoothPointAddition W p
        (Spec.map (CommRingCat.ofHom (a').toRingHom) ≫
          toCurve W s b3 b4 b6 h3 h4 h6) hb := by
  have hc' : Set.range (Spec.map (CommRingCat.ofHom (c').toRingHom) ≫
      toCurve W s b3 b4 b6 h3 h4 h6) ⊆
        WeierstrassIntegralChart.integralSmoothOpen W := by
    rw [hp]
    rintro _ ⟨z, rfl⟩
    exact (p z).property
  have hl : Spec.map (CommRingCat.ofHom ((c').comp orig).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        p ≫ (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
    rw [toCurve, ← Category.assoc, ← Spec.map_comp] at hp
    exact hp
  have hr : Spec.map (CommRingCat.ofHom ((a').comp orig).toRingHom) ≫
      WeierstrassIntegralChart.integralCurveChart W 2 =
        Spec.map (CommRingCat.ofHom (a').toRingHom) ≫
          toCurve W s b3 b4 b6 h3 h4 h6 := by
    rw [toCurve, ← Category.assoc, ← Spec.map_comp]
    rfl
  have hb' := hb
  rw [← hr] at hb'
  let v := dividedRightSmoothReciprocalPresentation W s b3 b4 b6 a c h3 h4 h6 e
    (by simpa only [AlgHom.comp_assoc] using hc')
  have hvL := dividedRightSmoothReciprocalPresentation_left W s b3 b4 b6 a c h3 h4 h6 e
    (by simpa only [AlgHom.comp_assoc] using hc')
  have hvR := dividedRightSmoothReciprocalPresentation_right W s b3 b4 b6 a c h3 h4 h6 e
    (by simpa only [AlgHom.comp_assoc] using hc')
  have he := WeierstrassIntegralChart.reciprocalPresentation_addition W
    ((c').comp orig) ((a').comp orig) false v
    (by simpa only [v, AlgHom.comp_assoc] using hvL)
    (by simpa only [v, AlgHom.comp_assoc] using hvR) p hl hb'
  simp only [hr] at he
  rw [dividedReciprocalToCurve, ← Category.assoc, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (e.comp (dividedReciprocalOutput W s b3 b4 b6 a c h3 h4 h6)).toRingHom) ≫ _ = _
  rw [← dividedRightSmoothReciprocalPresentation_output W s b3 b4 b6 a c h3 h4 h6 e
    (by simpa only [AlgHom.comp_assoc] using hc')]
  exact he

end FLT.Mazur.WeierstrassDilatation
