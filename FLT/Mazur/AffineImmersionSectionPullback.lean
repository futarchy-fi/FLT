/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineImmersionSectionCoordinates

/-!
# Pulling image-open sections back in their original coordinates

A commuting square of actual affine chart maps computes section pullback
by the original ring homomorphism, also when the ambient morphism moves charts.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.AffineImmersionSectionCoordinates

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable {X Y : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]
variable (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]
variable (g : Spec (.of B) ⟶ Y) [IsOpenImmersion g] (k : Y ⟶ X)
variable (σ : A →+* B) (h : Spec.map (CommRingCat.ofHom σ) ≫ f = g ≫ k)

include h in
/-- A square of original affine chart maps supplies the required image-open containment. -/
theorem image_le_preimage : (imageAffine g).1 ≤ k ⁻¹ᵁ (imageAffine f).1 := by
  rintro x ⟨y, _, rfl⟩
  exact ⟨Spec.map (CommRingCat.ofHom σ) y, trivial,
    congrArg (fun a : Spec (.of B) ⟶ X ↦ a y) h⟩

/-- The actual section pullback computes the given original coordinate homomorphism. -/
theorem coordinates_pullback (s : Γ(X, (imageAffine f).1)) :
    coordinates g (k.appLE (imageAffine f).1 (imageAffine g).1
      (image_le_preimage f g k σ h) s) = σ (coordinates f s) := by
  have he : k.appLE (imageAffine f).1 (imageAffine g).1
        (image_le_preimage f g k σ h) ≫ (g.appIso ⊤).hom =
      (f.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom σ)).appTop := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.appIso_hom', Scheme.Hom.appLE_comp_appLE]
    change _ = f.appLE _ ⊤ _ ≫ (Spec.map (CommRingCat.ofHom σ)).app ⊤
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    simp only [h]
    rfl
  have hh := congrArg (fun a ↦ a.hom s)
    (show k.appLE (imageAffine f).1 (imageAffine g).1
        (image_le_preimage f g k σ h) ≫ (g.appIso ⊤).hom ≫
          (Scheme.ΓSpecIso (.of B)).hom =
      (f.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom σ by
      rw [← Category.assoc, he, Category.assoc, Scheme.ΓSpecIso_naturality])
  exact hh

end FLT.Mazur.AffineImmersionSectionCoordinates
