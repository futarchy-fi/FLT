/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts

/-!
# Section coordinates on the image of an affine open immersion

The image-open section ring is the original affine coordinate ring. The
comparison intertwines restriction with the original coordinate homomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineImmersionSectionCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]

/-- The actual affine image open, retaining its affine proof. -/
abbrev imageAffine : X.affineOpens :=
  ⟨f ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion f⟩

/-- Coordinates on the image are the original affine ring, without a chosen presentation. -/
def coordinates : Γ(X, (imageAffine f).1) ≃+* A :=
  ((f.appIso ⊤) ≪≫ Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv

/-- The coordinate map takes the actual comapped ideal to the original image-open ideal. -/
theorem ideal_comap (I : X.IdealSheafData) :
    I.ideal (imageAffine f) =
      Ideal.comap (coordinates f).toRingHom
        (Ideal.map (Scheme.ΓSpecIso (.of A)).hom.hom
          ((I.comap f).ideal ⟨⊤, isAffineOpen_top _⟩)) := by
  let e := (f.appIso ⊤).commRingCatIsoToRingEquiv
  let d := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  rw [I.ideal_comap_of_isOpenImmersion]
  change _ = Ideal.comap (e.trans d).toRingHom
    (Ideal.map d.toRingHom (Ideal.comap e.symm.toRingHom _))
  simp only [RingEquiv.toRingHom_eq_coe, Ideal.map_comap_of_equiv]
  ext s
  change s ∈ I.ideal (imageAffine f) ↔
    e.symm (d.symm (d (e s))) ∈ I.ideal (imageAffine f)
  simp only [RingEquiv.symm_apply_apply]

variable (g : Spec (.of B) ⟶ X) [IsOpenImmersion g]
variable (σ : A →+* B) (h : Spec.map (CommRingCat.ofHom σ) ≫ f = g)

include h in
/-- A commuting affine chart map gives the actual inclusion of image opens. -/
theorem image_le : (imageAffine g).1 ≤ (imageAffine f).1 := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨Spec.map (CommRingCat.ofHom σ) y, trivial, by
    exact congrArg (fun k : Spec (.of B) ⟶ X ↦ k y) h⟩

/-- Restriction between the actual image opens is the supplied coordinate map. -/
theorem coordinates_restrict (s : Γ(X, (imageAffine f).1)) :
    coordinates g (X.presheaf.map (homOfLE (image_le f g σ h)).op s) =
      σ (coordinates f s) := by
  have he : X.presheaf.map (homOfLE (image_le f g σ h)).op ≫ (g.appIso ⊤).hom =
      (f.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom σ)).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    change _ = f.appLE _ ⊤ _ ≫
      (Spec.map (CommRingCat.ofHom σ)).app ⊤
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    subst g
    rfl
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom σ)
  have hh := congrArg (fun k ↦ k.hom s)
    (show X.presheaf.map (homOfLE (image_le f g σ h)).op ≫
        (g.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of B)).hom =
      (f.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom σ by
      rw [← Category.assoc, he, Category.assoc, hn])
  exact hh

end FLT.Mazur.AffineImmersionSectionCoordinates
