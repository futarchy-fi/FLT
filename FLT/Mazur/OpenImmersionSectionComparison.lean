/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# Global sections as ambient sections on an open image

The comparison for open immersions commutes with restriction along a triangle
of scheme maps. This supplies restriction compatibility for glued chart rings.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) [IsOpenImmersion f]

/-- Pulling back ambient sections on the image is the inverse comparison. -/
theorem openImageSectionIso_inv :
    (IsOpenImmersion.ΓIsoTop f).inv =
      f.appLE f.opensRange ⊤ (by intro x _; exact ⟨x, rfl⟩) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, Iso.symm_inv, Scheme.Hom.appIso_hom',
    Scheme.Hom.map_appLE]

variable (g : Y ⟶ Z) [IsOpenImmersion g] (k : Y ⟶ X) (h : k ≫ f = g)

include k h in
/-- A factorization through an open chart gives containment of images. -/
theorem openImage_le_of_comp : g.opensRange ≤ f.opensRange := by
  rintro _ ⟨y, rfl⟩
  exact ⟨k y, by rw [← Scheme.Hom.comp_apply, h]⟩

/-- The section isomorphisms carry a chart map to ambient restriction. -/
theorem openImageSectionIso_naturality :
    (IsOpenImmersion.ΓIsoTop f).hom ≫
        Z.presheaf.map (homOfLE (openImage_le_of_comp f g k h)).op =
      k.appTop ≫ (IsOpenImmersion.ΓIsoTop g).hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq, openImageSectionIso_inv,
    openImageSectionIso_inv, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  subst g
  rfl

end FLT.Mazur.Approximation
