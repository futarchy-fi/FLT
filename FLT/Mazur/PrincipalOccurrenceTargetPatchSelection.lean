/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCartesian
public import FLT.Mazur.PrincipalOccurrenceAtlasComparisons

/-!
# Selecting patches with routes into a prescribed ambient chart

Only patches whose outer label is incident to the target chart are used.
An original chart-cover inclusion proves that these constrained patches
cover the original overlap; no diagonal patches are inserted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))



/-- A patch together with a route from its outer overlap into a prescribed target chart. -/
abbrev PrincipalOccurrencePatchTo (j : κ) (i : ι) :=
  Σ p : PrincipalOccurrencePatch (dst := dst) j,
    {k : J i // dst i k = dst p.1.val.1 p.2}

/-- The constrained family is finite whenever the occurrence atlas is finite. -/
instance principalOccurrencePatchTo_finite [Finite ι] [∀ i, Finite (J i)] (j : κ) (i : ι) :
    Finite (PrincipalOccurrencePatchTo (dst := dst) j i) := inferInstance

/-- Pullback of the second original occurrence image is exactly the double-open patch. -/
theorem principalOccurrenceOriginalPatch_image_preimage (i : ι) (k l : J i) :
    (principalOccurrenceOriginalPatchOpen e ⟨⟨⟨i, k⟩, rfl⟩, l⟩).opensRange =
      principalOccurrenceOriginalOpen e i k ⁻¹ᵁ
        (principalOccurrenceOriginalOpen e i l).opensRange := by
  let H := principalOccurrenceOriginalPatch_isPullback e i k l
  have he := Scheme.Hom.opensRange_comp_of_isIso H.isoPullback.hom
    (pullback.fst (principalOccurrenceOriginalOpen e i k) (principalOccurrenceOriginalOpen e i l))
  simp only [H.isoPullback_hom_fst] at he
  rw [he, Scheme.Hom.opensRange_pullbackFst]

/-- A cover inclusion in an incoming chart gives a cover by its chosen double-open patches. -/
theorem principalOccurrenceOriginalPatch_cover_of_image_le (i : ι) (k : J i)
    {μ : Type*} (l : μ → J i)
    (hc : (principalOccurrenceOriginalOpen e i k).opensRange ≤
      ⨆ n, (principalOccurrenceOriginalOpen e i (l n)).opensRange) :
    (⨆ n, (principalOccurrenceOriginalPatchOpen e ⟨⟨⟨i, k⟩, rfl⟩, l n⟩).opensRange) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp (hc (show
    principalOccurrenceOriginalOpen e i k z ∈
      (principalOccurrenceOriginalOpen e i k).opensRange from ⟨z, rfl⟩))
  apply TopologicalSpace.Opens.mem_iSup.mpr
  refine ⟨n, ?_⟩
  rw [principalOccurrenceOriginalPatch_image_preimage]
  exact hn

/-- Original cover inclusions select a covering family whose every patch routes to the target. -/
theorem principalOccurrenceOriginalPatchTo_cover {j : κ} (i : ι)
    (c : PrincipalIncoming (dst := dst) j)
    (hc : (principalOccurrenceOriginalOpen e c.val.1 c.val.2).opensRange ≤
      ⨆ l : {l : J c.val.1 // ∃ k : J i, dst i k = dst c.val.1 l},
        (principalOccurrenceOriginalOpen e c.val.1 l.val).opensRange) :
    (⨆ p : PrincipalOccurrencePatchTo (dst := dst) j i,
      (principalOccurrenceOriginalPatchOpen e p.1).opensRange) = ⊤ := by
  classical
  obtain ⟨⟨i₀, k₀⟩, rfl⟩ := c
  have hcover := principalOccurrenceOriginalPatch_cover_of_image_le e i₀ k₀
    (fun l : {l : J i₀ // ∃ k : J i, dst i k = dst i₀ l} ↦ l.val) hc
  apply top_unique
  rw [← hcover]
  apply iSup_le
  intro l
  obtain ⟨k, hk⟩ := l.property
  exact le_iSup_of_le ⟨⟨⟨⟨i₀, k₀⟩, rfl⟩, l.val⟩, ⟨k, hk⟩⟩ le_rfl

end FLT.Mazur.FiniteTypeRelationModel
