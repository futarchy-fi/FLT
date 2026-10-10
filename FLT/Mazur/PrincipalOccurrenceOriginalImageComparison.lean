/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceTargetPatchSelection

/-!
# Original patch images in the actual scheme atlas

A patch image depends only on its two overlap images in the original
scheme. The incoming ambient chart cancels because it is an open immersion.
This supplies image inclusions, including comparisons of opposite routes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  {X : Scheme.{u}} (U : ∀ i, Spec (.of (A i)) ⟶ X)
  (V : ∀ j, Spec (.of (Localization.Away (b j))) ⟶ X)
  [∀ i, IsOpenImmersion (U i)] [∀ j, IsOpenImmersion (V j)]
  (hUV : ∀ i k, principalOccurrenceOriginalOpen e i k ≫ U i = V (dst i k))

include hUV in
/-- Patch images are the inverse images of the outer overlap in the actual scheme. -/
theorem principalOccurrenceOriginalPatch_image_atlas {j : κ}
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    (principalOccurrenceOriginalPatchOpen e p).opensRange =
      V j ⁻¹ᵁ (V (dst p.1.val.1 p.2)).opensRange := by
  obtain ⟨⟨⟨i, k⟩, rfl⟩, l⟩ := p
  rw [principalOccurrenceOriginalPatch_image_preimage]
  ext z
  change (∃ w, principalOccurrenceOriginalOpen e i l w =
    principalOccurrenceOriginalOpen e i k z) ↔ ∃ w, V (dst i l) w = V (dst i k) z
  have hk := congrArg (fun g ↦ g z) (hUV i k)
  constructor
  · rintro ⟨w, hw⟩
    have hl := congrArg (fun g ↦ g w) (hUV i l)
    exact ⟨w, hl.symm.trans ((congrArg (U i) hw).trans hk)⟩
  · rintro ⟨w, hw⟩
    have hl := congrArg (fun g ↦ g w) (hUV i l)
    exact ⟨w, (U i).isOpenEmbedding.injective (hl.trans (hw.trans hk.symm))⟩

include hUV in
/-- An inclusion of outer overlap images gives the needed original patch image inclusion. -/
theorem principalOccurrenceOriginalPatch_image_le {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j)
    (h : (V (dst p.1.val.1 p.2)).opensRange ≤ (V (dst q.1.val.1 q.2)).opensRange) :
    (principalOccurrenceOriginalPatchOpen e p).opensRange ≤
      (principalOccurrenceOriginalPatchOpen e q).opensRange := by
  rw [principalOccurrenceOriginalPatch_image_atlas e U V hUV,
    principalOccurrenceOriginalPatch_image_atlas e U V hUV]
  exact fun _ hz ↦ h hz

include hUV in
/-- Opposite incoming charts give identical patches when their outer label agrees. -/
theorem principalOccurrenceOriginalPatch_image_eq {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j)
    (h : dst p.1.val.1 p.2 = dst q.1.val.1 q.2) :
    (principalOccurrenceOriginalPatchOpen e p).opensRange =
      (principalOccurrenceOriginalPatchOpen e q).opensRange := by
  rw [principalOccurrenceOriginalPatch_image_atlas e U V hUV,
    principalOccurrenceOriginalPatch_image_atlas e U V hUV, h]

end FLT.Mazur.FiniteTypeRelationModel
