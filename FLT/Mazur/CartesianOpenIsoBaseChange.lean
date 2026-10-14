/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Transporting actual unchanged opens through Cartesian squares

Restrict a specified Cartesian square to an actual target open. If the original
map is an isomorphism there, so is the specified map on its full inverse image.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CartesianOpenIsoBaseChange

variable {X Y X' Y' : Scheme} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {a : X' ⟶ X} {b : Y' ⟶ Y} (H : IsPullback f' a b f) (U : Y.Opens)

include H in
/-- Isomorphism on a full target open survives any specified Cartesian change of base. -/
theorem isIso_restrict [IsIso (f ∣_ U)] : IsIso (f' ∣_ b ⁻¹ᵁ U) := by
  have he : f' ⁻¹ᵁ (b ⁻¹ᵁ U) = a ⁻¹ᵁ (f ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage]
  have hs := Scheme.Hom.isPullback_resLE H (US := U) (UT := f ⁻¹ᵁ U)
    (UX := b ⁻¹ᵁ U) le_rfl le_rfl (UY := f' ⁻¹ᵁ (b ⁻¹ᵁ U))
    (by rw [he, inf_idem])
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at hs
  exact hs.isIso_fst_of_isIso

end FLT.Mazur.CartesianOpenIsoBaseChange
