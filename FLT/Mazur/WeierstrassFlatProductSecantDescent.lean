/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSecantMorphismExt

/-!
# Secant descent after a flat change of the input scheme

The dense affine overlaps and the regular secant denominator remain
schematically dense under flat pullback. Thus secant presentations detect
maps to any separated target, including on the full smooth product open.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The other projection of each actual product overlap is an open immersion. -/
theorem integralProductOverlapSnd_open (b c d e : Bool) :
    IsOpenImmersion (integralProductOverlapSnd W b c d e) :=
  IsOpenImmersion.of_isPullback (integralProductOverlap_isPullback W b c d e)
    inferInstance

/-- Flat input schemes can be tested on their actual affine presentations. -/
theorem flatProduct_hom_ext_affine {T X B : Scheme.{u}}
    (t : T ⟶ integralCurveProduct W) [Flat t] (s : X ⟶ B) [IsSeparated s]
    (f g : T ⟶ X) (hb : f ≫ s = g ≫ s)
    (ha : ∀ (U : Scheme.{u}) (p : U ⟶ T)
      (a : U ⟶ Spec (.of (AffineProduct W))), Flat a →
      a ≫ integralCurveProductChart W false false = p ≫ t → p ≫ f = p ≫ g) :
    f = g := by
  let C := integralCurveProductCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ t)
  rintro ⟨b, c⟩
  let p := (C.pullback₁ t).f (b, c)
  let q := Scheme.Cover.pullbackHom C t (b, c)
  have hq : q ≫ integralCurveProductChart W b c = p ≫ t :=
    Scheme.Cover.pullbackHom_map C t (b, c)
  let _ : Flat q := by
    dsimp [q, Scheme.Cover.pullbackHom]
    infer_instance
  let r := integralProductOverlapFst W b c false false
  let v := integralProductOverlapSnd W b c false false
  let _ : IsSchemeTheoreticallyDominant r :=
    SurjectiveDominantEpi.spec_schematic
      (productOverlapRestriction W (productChartCoordinate b)
        (productChartCoordinate c) 2 2).toRingHom (productAffineOverlap_injective W b c)
  let _ : IsOpenImmersion v := integralProductOverlapSnd_open W b c false false
  apply Chow.schematicallyDense_ext s
    (by simpa only [Category.assoc] using congrArg (p ≫ ·) hb) (pullback.snd r q)
  have he : (pullback.fst r q ≫ v) ≫ integralCurveProductChart W false false =
      (pullback.snd r q ≫ p) ≫ t := by
    rw [Category.assoc, ← integralProductOverlap_condition,
      ← Category.assoc, pullback.condition, Category.assoc, hq, Category.assoc]
  simpa only [Category.assoc] using
    ha _ (pullback.snd r q ≫ p) (pullback.fst r q ≫ v) inferInstance he

/-- The original secant formula detects maps after every flat input change. -/
theorem flatProduct_hom_ext_secant {T X B : Scheme.{u}}
    (t : T ⟶ integralCurveProduct W) [Flat t] (s : X ⟶ B) [IsSeparated s]
    (f g : T ⟶ X) (hb : f ≫ s = g ≫ s)
    (hs : ∀ (U : Scheme.{u}) (p : U ⟶ T) (a : U ⟶ Spec (.of (SecantChart W))),
      a ≫ Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
        integralCurveProductChart W false false = p ≫ t → p ≫ f = p ≫ g) : f = g := by
  apply flatProduct_hom_ext_affine W t s f g hb
  intro U p a ha he
  let _ := ha
  let r := Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom)
  let _ : IsSchemeTheoreticallyDominant r :=
    SurjectiveDominantEpi.spec_schematic (secantRestriction W).toRingHom
      (secantRestriction_injective W)
  apply Chow.schematicallyDense_ext s
    (by simpa only [Category.assoc] using congrArg (p ≫ ·) hb) (pullback.snd r a)
  have hh : pullback.fst r a ≫ r ≫ integralCurveProductChart W false false =
      (pullback.snd r a ≫ p) ≫ t := by
    rw [← Category.assoc, pullback.condition, Category.assoc, he, Category.assoc]
  simpa only [Category.assoc] using hs _ (pullback.snd r a ≫ p) (pullback.fst r a) hh

end FLT.Mazur.WeierstrassIntegralChart
