/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineImmersionSectionCoordinates

/-!
# Section transport from an affine chart through an open factor

The original coordinate homomorphism computes pullback of image-open sections.
An open factor computes the same pullback using its actual top-open transport.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineImmersionSectionCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {X : Scheme.{u}} {A B : Type u} [CommRing A] [CommRing B]

/-- Pullback of an image-open section uses the original affine coordinate map. -/
theorem coordinates_appLE (f : Spec (.of A) ⟶ X) [IsOpenImmersion f]
    (σ : A →+* B) (b : Spec (.of B) ⟶ X)
    (hb : Spec.map (CommRingCat.ofHom σ) ≫ f = b)
    (hU : ⊤ ≤ b ⁻¹ᵁ (imageAffine f).1) (s : Γ(X, (imageAffine f).1)) :
    (Scheme.ΓSpecIso (.of B)).hom (b.appLE _ ⊤ hU s) = σ (coordinates f s) := by
  subst b
  have he : (f.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom σ)).appTop =
      (Spec.map (CommRingCat.ofHom σ) ≫ f).appLE _ ⊤ hU := by
    rw [Scheme.Hom.appIso_hom']
    change f.appLE _ ⊤ _ ≫ (Spec.map (CommRingCat.ofHom σ)).app ⊤ = _
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    rfl
  have hn := congrArg (fun k ↦ k.hom s)
    (show (f.appIso ⊤).hom ≫ (Spec.map (CommRingCat.ofHom σ)).appTop ≫
        (Scheme.ΓSpecIso (.of B)).hom =
      (f.appIso ⊤).hom ≫ (Scheme.ΓSpecIso (.of A)).hom ≫ CommRingCat.ofHom σ by
      rw [Scheme.ΓSpecIso_naturality])
  rw [← Category.assoc, he] at hn
  exact hn

/-- An actual factor through an open gives its top-section pullback without new frames. -/
theorem openFactor_appTop (U : X.Opens) (q : Spec (.of B) ⟶ U.toScheme)
    (hU : ⊤ ≤ (q ≫ U.ι) ⁻¹ᵁ U) :
    U.topIso.inv ≫ q.appTop = (q ≫ U.ι).appLE U ⊤ hU := by
  have he := Scheme.Hom.appLE_comp_appLE q U.ι U ⊤ ⊤
    (by rw [Scheme.Opens.ι_preimage_self]) (by simp)
  have hu : U.ι.appLE U ⊤ (by rw [Scheme.Opens.ι_preimage_self]) =
      U.topIso.inv := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    congr 1
  rw [hu] at he
  simpa [Scheme.Hom.appLE, Scheme.Hom.appTop] using he

end FLT.Mazur.AffineImmersionSectionCoordinates
