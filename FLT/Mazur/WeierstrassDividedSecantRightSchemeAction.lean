/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecantReverse

/-!
# The original right smooth action for arbitrary supplied secants

Reverse the actual secant localization and use the constructed left action.
Both original inputs and the entire original cubic output are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a c : Coordinate W s b3 b4 b6 →ₐ[R] S)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
local notation "T" => DividedSecantRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "l" => Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom)
local notation "r" => Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom)
local notation "v" => toCurve W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- The secant formula agrees with the smooth action based at the right original input. -/
theorem dividedSecant_rightSchemeAction {X : Scheme.{u}} (f : X ⟶ Spec (.of T))
    (p : X ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ r ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ l ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedSecantToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ l ≫ v) hb := by
  let z := Spec.map (CommRingCat.ofHom (dividedSecantReverse W s b3 b4 b6 a c).toRingHom)
  let e := IsScalarTower.toAlgHom R S (DividedSecantRing W s b3 b4 b6 c a)
  have he (b : Coordinate W s b3 b4 b6 →ₐ[R] S) :
      z ≫ Spec.map (CommRingCat.ofHom (e.comp b).toRingHom) =
        Spec.map (CommRingCat.ofHom ((j).comp b).toRingHom) := by
    have hz : z ≫ Spec.map (CommRingCat.ofHom e.toRingHom) =
        Spec.map (CommRingCat.ofHom (j).toRingHom) :=
      dividedSecantReverse_spec_base W s b3 b4 b6 a c
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using
      congrArg (· ≫ Spec.map (CommRingCat.ofHom b.toRingHom)) hz
  have hp' : (f ≫ z) ≫ Spec.map (CommRingCat.ofHom (e.comp c).toRingHom) ≫ v =
      p ≫ (integralSmoothOpen W).ι := by
    simpa only [Category.assoc, reassoc_of% he c] using hp
  have hb' : p ≫ integralSmoothStructure W =
      ((f ≫ z) ≫ Spec.map (CommRingCat.ofHom (e.comp a).toRingHom) ≫ v) ≫
        integralCurveStructure W := by
    simpa only [Category.assoc, reassoc_of% he a] using hb
  have h := dividedSecant_schemeAction W s b3 b4 b6 c a h3 h4 h6 (f ≫ z) p hp' hb'
  dsimp only [e, z] at he
  simpa only [z, Category.assoc, dividedSecantReverse_toCurve, reassoc_of% he a] using h

end FLT.Mazur.WeierstrassDilatation
