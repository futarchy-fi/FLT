/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassCoefficientModelProjection
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq

/-!
# Composition of full coefficient presentations

The concrete generalized-curve comparison commutes with arbitrary towers of
coefficient homomorphisms, retaining all named-equation equality transports.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientPresentationIso
/-- Two full maps to an iterated pullback agree if their original curve projections agree. -/
theorem coefficientTower_hom_ext {S T U : Scheme} (E : GeneralizedEllipticCurve S)
    (f : T ⟶ S) (g : U ⟶ T) {D : GeneralizedEllipticCurve U}
    (a b : D ⟶ (E.baseChange f).baseChange g)
    (h : a.curve.left ≫ pullback.fst _ g ≫ pullback.fst _ f =
      b.curve.left ≫ pullback.fst _ g ≫ pullback.fst _ f) : a = b := by
  apply baseChange_hom_ext
  apply pullback.hom_ext h
  have hw := a.curve.w.trans b.curve.w.symm
  change a.curve.left ≫ pullback.snd (pullback.snd E.curve.hom f) g =
    b.curve.left ≫ pullback.snd (pullback.snd E.curve.hom f) g at hw
  change a.curve.left ≫ pullback.fst (pullback.snd _ f) g ≫ pullback.snd _ f =
    b.curve.left ≫ pullback.fst (pullback.snd _ f) g ≫ pullback.snd _ f
  rw [pullback.condition]
  simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ g) hw

/-- The original curve projections determine the coherence of three full presentations. -/
theorem coefficientTower_comp_of_projection {S T U : Scheme}
    (E : GeneralizedEllipticCurve S) (F : GeneralizedEllipticCurve T)
    (G : GeneralizedEllipticCurve U) (f : T ⟶ S) (g : U ⟶ T) (h : U ⟶ S)
    (w : h = g ≫ f) (e : F ≅ E.baseChange f) (d : G ≅ F.baseChange g)
    (c : G ≅ E.baseChange h)
    (hc : c.hom.curve.left ≫ pullback.fst _ h =
      (d.hom.curve.left ≫ pullback.fst _ g) ≫
        (e.hom.curve.left ≫ pullback.fst _ f)) :
    c.hom ≫ (E.baseChangeCompEqIso f g h w).hom = d.hom ≫ baseChangeMap g e.hom := by
  apply coefficientTower_hom_ext
  change c.hom.curve.left ≫ (E.baseChangeCompEqIso f g h w).hom.curve.left ≫
      pullback.fst _ g ≫ pullback.fst _ f =
    d.hom.curve.left ≫ (baseChangeMap g e.hom).curve.left ≫
      pullback.fst _ g ≫ pullback.fst _ f
  rw [baseChangeCompEqIso_curve_fst, baseChangeMap_fst_assoc]
  exact hc.trans (Category.assoc _ _ _)

variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
  (W : WeierstrassCurve R) (V : WeierstrassCurve A) (Z : WeierstrassCurve B)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (hZ : IsUnit Z.Δ)
  (f : R →+* A) (g : A →+* B)
  (hf : V = W.map f) (hg : Z = V.map g) (hgf : Z = W.map (g.comp f))
local notation "E" => integralGeneralizedEllipticCurve W hW
local notation "kf" => Spec.map (CommRingCat.ofHom f)
local notation "kg" => Spec.map (CommRingCat.ofHom g)
local notation "kgf" => Spec.map (CommRingCat.ofHom (g.comp f))

/-- Direct and iterated coefficient comparisons agree as full generalized-curve maps. -/
theorem coefficientPresentationIso_comp :
    (coefficientPresentationIso W hW (g.comp f) Z hZ hgf).hom ≫
      ((E).baseChangeCompEqIso kf kg kgf (Spec.map_comp _ _)).hom =
    (coefficientPresentationIso V hV g Z hZ hg).hom ≫
      baseChangeMap kg (coefficientPresentationIso W hW f V hV hf).hom := by
  apply coefficientTower_comp_of_projection
  exact (coefficientPresentationIso_fst W hW (g.comp f) Z hZ hgf).trans
    ((properCoefficientMap_comp W V Z f g hf hg hgf).symm.trans
      (congrArg₂ (fun x y ↦ x ≫ y)
        (coefficientPresentationIso_fst V hV g Z hZ hg).symm
        (coefficientPresentationIso_fst W hW f V hV hf).symm))

end FLT.Mazur.WeierstrassIntegralChart
