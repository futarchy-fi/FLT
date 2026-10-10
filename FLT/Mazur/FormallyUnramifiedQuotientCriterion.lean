/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# A quotient test for formal unramifiedness

It suffices to check uniqueness on square-zero quotient maps themselves.
This avoids choosing an isomorphism from the quotient by the kernel for each
surjection and agrees directly with the algebraic infinitesimal criterion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FormallyUnramifiedQuotientCriterion

universe u
variable {X Y : Scheme.{u}}

/-- Uniqueness across square-zero quotient spectra implies formal unramifiedness. -/
theorem of_quotient_hom_ext (f : X ⟶ Y)
    (H : ∀ (A : Type u) [CommRing A] (I : Ideal A), I ^ 2 = ⊥ →
      ∀ (g₁ g₂ : Spec (.of A) ⟶ X),
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g₁ =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ g₂ →
        g₁ ≫ f = g₂ ≫ f → g₁ = g₂) : FormallyUnramified f := by
  refine ⟨fun {U hU V hV hVU} ↦ ?_⟩
  let _ := (f.appLE U V hVU).hom.toAlgebra
  refine Algebra.FormallyUnramified.iff_comp_injective.mpr fun A _ _ I hI g₁ g₂ hg ↦ ?_
  have hg₁ : f.appLE U V hVU ≫ CommRingCat.ofHom g₁ =
      CommRingCat.ofHom (algebraMap _ A) := CommRingCat.hom_ext g₁.comp_algebraMap
  have hg₂ : f.appLE U V hVU ≫ CommRingCat.ofHom g₂ =
      CommRingCat.ofHom (algebraMap _ A) := CommRingCat.hom_ext g₂.comp_algebraMap
  have he := H A I hI
    (Spec.map (CommRingCat.ofHom g₁) ≫ hV.fromSpec)
    (Spec.map (CommRingCat.ofHom g₂) ≫ hV.fromSpec)
    (by
      simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      exact DFunLike.congr_fun hg x)
    (by simp only [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU,
      ← Spec.map_comp_assoc, hg₁, hg₂])
  rw [cancel_mono, Spec.map_inj] at he
  exact AlgHom.ext fun x ↦ congr($he x)

end FLT.Mazur.FormallyUnramifiedQuotientCriterion
