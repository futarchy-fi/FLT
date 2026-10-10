/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Full unchanged opens and their local recognition

An identity pullback over an open immersion proves that the entire inverse
image is unchanged. These comparisons descend to smaller opens and glue
pointwise, so they can identify an actual smooth open rather than one chart.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.SchemeUnchangedOpen
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme} (f : X ⟶ Y)

/-- A full identity pullback makes the restriction to the chart image an isomorphism. -/
theorem isIso_of_identity_pullback (i : T ⟶ Y) [IsOpenImmersion i] (j : T ⟶ X)
    (h : IsPullback (𝟙 T) j i f) : IsIso (f ∣_ i.opensRange) := by
  have hi : IsIso (pullback.snd f i) := by
    rw [← h.flip.isoPullback_inv_snd]
    infer_instance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictOpensRange f i)).mpr hi

/-- Being unchanged persists on every smaller target open. -/
theorem isIso_of_le {U V : Y.Opens} (hUV : U ≤ V) (h : IsIso (f ∣_ V)) :
    IsIso (f ∣_ U) := by
  have hr := IsZariskiLocalAtTarget.restrict (P := .isomorphisms Scheme) h (V.ι ⁻¹ᵁ U)
  have he : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hUV]
  have hh := ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp hr
  rwa [he] at hh

/-- An open is unchanged if each of its points has an unchanged target neighborhood. -/
theorem isIso_of_neighborhoods (U : Y.Opens)
    (h : ∀ y ∈ U, ∃ V : Y.Opens, y ∈ V ∧ IsIso (f ∣_ V)) : IsIso (f ∣_ U) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
    (P := .isomorphisms Scheme)
  intro y
  obtain ⟨V, hy, hV⟩ := h y.val y.property
  refine ⟨U.ι ⁻¹ᵁ V, hy, ?_⟩
  apply ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict f U (U.ι ⁻¹ᵁ V))).mpr
  apply isIso_of_le f _ hV
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
  exact inf_le_right

end FLT.Mazur.SchemeUnchangedOpen
