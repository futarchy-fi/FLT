/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentOriginalAction
public import FLT.Mazur.WeierstrassLeftSmoothInverseAction

/-!
# Scheme-valued overlap comparison for divided tangents

Recover coefficient algebras on affine charts from the actual tangent-source
map. The affine comparison then descends to every test scheme, with no
flatness, reducedness, or preselected affine presentation required.
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
local notation "T" => DividedTangentRing W s b3 b4 b6 a c
local notation "j" => IsScalarTower.toAlgHom R S T
local notation "l" => Spec.map (CommRingCat.ofHom ((j).comp a).toRingHom)
local notation "r" => Spec.map (CommRingCat.ofHom ((j).comp c).toRingHom)
local notation "v" => toCurve W s b3 b4 b6 h3 h4 h6
open WeierstrassIntegralChart

/-- Every affine scheme map into the tangent source has the actual original smooth action. -/
theorem dividedTangent_affineSchemeAction {B : Type u} [CommRing B]
    (f : Spec (.of B) ⟶ Spec (.of T))
    (p : Spec (.of B) ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ l ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ r ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ r ≫ v) hb := by
  let g : T →+* B := (Spec.preimage f).hom
  let _ : Algebra R B := (g.comp (algebraMap R T)).toAlgebra
  let e : T →ₐ[R] B := { g with commutes' := fun _ => rfl }
  have he : Spec.map (CommRingCat.ofHom e.toRingHom) = f := Spec.map_preimage f
  have hl : Spec.map (CommRingCat.ofHom ((e.comp j).comp a).toRingHom) = f ≫ l := by
    rw [← he, ← Spec.map_comp]
    rfl
  have hr : Spec.map (CommRingCat.ofHom ((e.comp j).comp c).toRingHom) = f ≫ r := by
    rw [← he, ← Spec.map_comp]
    rfl
  have hp' : Spec.map (CommRingCat.ofHom ((e.comp j).comp a).toRingHom) ≫ v =
      p ≫ (integralSmoothOpen W).ι := by rw [hl, Category.assoc]; exact hp
  have hb' : p ≫ integralSmoothStructure W =
      (Spec.map (CommRingCat.ofHom ((e.comp j).comp c).toRingHom) ≫ v) ≫
        integralCurveStructure W := by rw [hr, Category.assoc]; exact hb
  have h := dividedTangentRefinement_originalAction W s b3 b4 b6 a c h3 h4 h6 e p hp' hb'
  simpa only [he, hr, Category.assoc] using h

/-- The original action comparison holds on arbitrary scheme refinements of the tangent. -/
theorem dividedTangent_schemeAction {X : Scheme.{u}} (f : X ⟶ Spec (.of T))
    (p : X ⟶ (integralSmoothOpen W).toScheme)
    (hp : f ≫ l ≫ v = p ≫ (integralSmoothOpen W).ι)
    (hb : p ≫ integralSmoothStructure W = (f ≫ r ≫ v) ≫ integralCurveStructure W) :
    f ≫ dividedTangentToCurve W s b3 b4 b6 a c h3 h4 h6 =
      leftSmoothPointAddition W p (f ≫ r ≫ v) hb := by
  apply X.affineCover.hom_ext
  intro i
  let k := (X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i
  apply (cancel_epi (X.affineCover.X i).isoSpec.inv).mp
  have hp' : (k ≫ f) ≫ l ≫ v = (k ≫ p) ≫ (integralSmoothOpen W).ι := by
    simp only [Category.assoc, hp]
  have hb' : (k ≫ p) ≫ integralSmoothStructure W =
      ((k ≫ f) ≫ r ≫ v) ≫ integralCurveStructure W := by
    simp only [Category.assoc, hb]
  have h := dividedTangent_affineSchemeAction W s b3 b4 b6 a c h3 h4 h6
    (k ≫ f) (k ≫ p) hp' hb'
  have hc := leftSmoothPointAddition_comp W k p (f ≫ r ≫ v) hb
  simp only [Category.assoc] at h hc
  rw [hc] at h
  simpa only [k, Category.assoc] using h

end FLT.Mazur.WeierstrassDilatation
