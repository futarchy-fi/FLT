/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLocalizationPullback

/-!
# Principal localization intersections inside an ambient scheme

An affine base-change square remains cartesian after embedding its target in
an ambient scheme. Its affine source computes sections of the actual open
intersection, not just of an abstract pullback.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PrincipalLocalizationIntersection
open PrincipalAffineRefinement LocalizationJointRestriction
variable {R S : Type u} [CommRing R] [CommRing S] {X : Scheme.{u}}

/-- Compose the affine localization square with an ambient monomorphism. -/
lemma isPullback (f : R →+* S) (s : R) (j : Spec (.of R) ⟶ X) [Mono j] :
    IsPullback (Spec.map (CommRingCat.ofHom (restriction f s))) (inclusion (f s))
      (chart j s) (Spec.map (CommRingCat.ofHom f) ≫ j) := by
  have hb : IsPullback (Spec.map (CommRingCat.ofHom f)) (𝟙 _) j
      (Spec.map (CommRingCat.ofHom f) ≫ j) :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  simpa only [Category.comp_id, chart] using
    (PrincipalLocalizationPullback.isPullback f s).flip.paste_vert hb

/-- The two-step affine open, in the coordinates of the second affine chart. -/
def overlap (f : R →+* S) (s : R) (j : Spec (.of R) ⟶ X) :
    Spec (.of (Localization.Away (f s))) ⟶ X :=
  inclusion (f s) ≫ Spec.map (CommRingCat.ofHom f) ≫ j

instance overlap_isOpenImmersion (f : R →+* S) (s : R) (j : Spec (.of R) ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (overlap f s j) := by unfold overlap; infer_instance

/-- The image is precisely the intersection of the two actual chart images. -/
lemma overlap_image (f : R →+* S) (s : R) (j : Spec (.of R) ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    overlap f s j ''ᵁ ⊤ =
      (chart j s ''ᵁ ⊤) ⊓ ((Spec.map (CommRingCat.ofHom f) ≫ j) ''ᵁ ⊤) := by
  let H := isPullback f s j
  have he : overlap f s j = H.isoPullback.hom ≫
      pullback.fst (chart j s) (Spec.map (CommRingCat.ofHom f) ≫ j) ≫ chart j s := by
    rw [← Category.assoc, H.isoPullback_hom_fst, H.w]
    rfl
  simp only [Scheme.Hom.image_top_eq_opensRange]
  ext x
  change x ∈ Set.range (overlap f s j) ↔
    x ∈ Set.range (chart j s) ∩ Set.range (Spec.map (CommRingCat.ofHom f) ≫ j)
  have hs : Function.Surjective H.isoPullback.hom := H.isoPullback.hom.homeomorph.surjective
  rw [he, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr hs, Set.image_univ]
  rw [IsOpenImmersion.range_pullback_to_base_of_left]

/-- Sections on the genuine intersection have the expected localized ring. -/
def sectionsIso (f : R →+* S) (s : R) (j : Spec (.of R) ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    Γ(X, (chart j s ''ᵁ ⊤) ⊓ ((Spec.map (CommRingCat.ofHom f) ≫ j) ''ᵁ ⊤)) ≅
      CommRingCat.of (Localization.Away (f s)) :=
  X.presheaf.mapIso (eqToIso (overlap_image f s j)).op ≪≫
    (overlap f s j).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

end FLT.Mazur.PrincipalLocalizationIntersection
