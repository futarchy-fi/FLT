/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenImageSectionPullback
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Section pullback on an actual open subscheme

For a commuting chart square whose source chart is an open subscheme, the
ambient section pullback is the chart pullback followed by the top-section
comparison. This avoids transporting through the open image of the inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {X Y Z : Scheme.{u}} (U : X.Opens) (k : Z ⟶ Y) [IsOpenImmersion k]
  (f : X ⟶ Y) (a : U.toScheme ⟶ Z) (h : U.ι ≫ f = a ≫ k)

include a h in
/-- The original open lies in the inverse image of the target chart. -/
theorem openChart_le_preimage : U ≤ f ⁻¹ᵁ k.opensRange := by
  simpa only [Scheme.Opens.opensRange_ι] using openImage_le_preimage U.ι k f a h

/-- Pullback of ambient chart sections onto an actual open subscheme. -/
theorem openChartSectionIso_pullback :
    (IsOpenImmersion.ΓIsoTop k).hom ≫
        f.appLE k.opensRange U (openChart_le_preimage U k f a h) =
      a.appTop ≫ U.topIso.hom := by
  rw [← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq, openImageSectionIso_inv]
  have ht : U.topIso.inv = U.ι.appLE U ⊤ (by simp) := by
    simp only [Scheme.Opens.ι_appLE, Scheme.Opens.topIso_inv]
    rfl
  rw [ht, Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 1

end FLT.Mazur.Approximation
