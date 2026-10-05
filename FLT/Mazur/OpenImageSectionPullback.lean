/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImmersionSectionComparison

/-!
# Pulling ambient chart sections through a commuting square

The open-image section isomorphism is compatible with arbitrary maps of
charts. No open-immersion assumption is imposed on the base-change map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {X Y U V : Scheme.{u}} (j : U ⟶ X) (k : V ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k]
  (f : X ⟶ Y) (a : U ⟶ V) (h : j ≫ f = a ≫ k)

include a h in
/-- A commuting square carries the source chart image into the target chart image. -/
theorem openImage_le_preimage : j.opensRange ≤ f ⁻¹ᵁ k.opensRange := by
  rintro _ ⟨x, rfl⟩
  exact ⟨a x, by simpa only [Scheme.Hom.comp_apply] using
    (congrArg (fun m : U ⟶ Y ↦ m x) h).symm⟩

/-- Ambient pullback on chart images is the coordinate pullback on global sections. -/
theorem openImageSectionIso_pullback :
    (IsOpenImmersion.ΓIsoTop k).hom ≫
        f.appLE k.opensRange j.opensRange (openImage_le_preimage j k f a h) =
      a.appTop ≫ (IsOpenImmersion.ΓIsoTop j).hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq,
    openImageSectionIso_inv, openImageSectionIso_inv,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 1

/-- Elementwise form of the chart pullback comparison. -/
theorem openImageSectionIso_pullback_apply (x : Γ(V, ⊤)) :
    f.appLE k.opensRange j.opensRange (openImage_le_preimage j k f a h)
        ((IsOpenImmersion.ΓIsoTop k).hom x) =
      (IsOpenImmersion.ΓIsoTop j).hom (a.appTop x) :=
  congrArg (fun m ↦ m x) (openImageSectionIso_pullback j k f a h)

end FLT.Mazur.Approximation
