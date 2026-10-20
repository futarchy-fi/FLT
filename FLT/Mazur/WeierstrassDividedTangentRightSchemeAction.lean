/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentRightChartAction
public import FLT.Mazur.WeierstrassDividedTangentReverseCoverMaps
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# The tangent formula agrees with the original right smooth action

Pulling back the constructed two-member cover proves the right-action
comparison on every scheme. Neither the tangent open nor its denominator
is asserted invariant under exchanging the inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "l" => Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom)
local notation "r" => Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom)
local notation "v" => toCurve W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- The actual tangent output agrees with the right action of any originally smooth input. -/
theorem dividedTangent_rightSchemeAction {X : Scheme.{u}} (f : X ⟶ Spec (.of T))
    (p : X ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ r ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ l ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ l ≫ v) hb := by
  let C := dividedTangentReverseCover W s b3 b4 b6 a c
  apply Scheme.Cover.hom_ext (C.openCover.pullback₁ f)
  intro b
  change Bool at b
  let k := pullback.fst f (C.f b)
  let m := pullback.snd f (C.f b)
  have hkm : m ≫ C.f b = k ≫ f := pullback.condition.symm
  have hp' : (k ≫ f) ≫ r ≫ v = (k ≫ p) ≫ (integralSmoothOpen W).ι := by
    simp only [Category.assoc, hp]
  have hb' : (k ≫ p) ≫ integralSmoothStructure W =
      ((k ≫ f) ≫ l ≫ v) ≫ integralCurveStructure W := by
    simp only [Category.assoc, hb]
  have hc := leftSmoothPointAddition_comp W k p (f ≫ l ≫ v) hb
  change k ≫ f ≫ _ = k ≫ leftSmoothPointAddition W p (f ≫ l ≫ v) hb
  rw [← hc]
  cases b
  · let g := m ≫ Spec.map (CommRingCat.ofHom
      (dividedTangentReverseCoverSecant W s b3 b4 b6 a c).toRingHom)
    have hg : g ≫ Spec.map (CommRingCat.ofHom
        (algebraMap S (DividedSecantRing W s b3 b4 b6 c a))) =
          (k ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
      dsimp only [g]
      rw [Category.assoc, dividedTangentReverseCoverSecant_spec,
        ← Category.assoc, hkm]
    simpa only [Category.assoc] using
      dividedTangent_rightSecantAction W s b3 b4 b6 a c h3 h4 h6 (k ≫ f) g hg (k ≫ p) hp' hb'
  · let g := m ≫ Spec.map (CommRingCat.ofHom
      (dividedTangentReverseCoverTangent W s b3 b4 b6 a c).toRingHom)
    have hg : g ≫ Spec.map (CommRingCat.ofHom
        (algebraMap S (DividedTangentRing W s b3 b4 b6 c a))) =
          (k ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
      dsimp only [g]
      rw [Category.assoc, dividedTangentReverseCoverTangent_spec,
        ← Category.assoc, hkm]
    simpa only [Category.assoc] using
      dividedTangent_rightTangentAction W s b3 b4 b6 a c h3 h4 h6 (k ≫ f) g hg (k ≫ p) hp' hb'

end FLT.Mazur.WeierstrassDilatation
