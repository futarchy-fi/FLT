/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceAmbientUnion

/-!
# Exact recovery of ambient occurrence image unions

Each original occurrence is the base change of its finite-stage embedding.
Taking unions therefore recovers the entire original union, not merely a
map whose image contains the original overlaps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
  (hx : ∀ i k, Function.Bijective (x.hom i k))


/-- Identifying an original literal overlap label preserves its open embedding. -/
instance principalOccurrenceOriginalOpenAt_isOpenImmersion {j : κ}
    (i : ι) (k : J i) (h : dst i k = j) :
    IsOpenImmersion (principalOccurrenceOriginalOpenAt e i k h) := by
  subst j
  exact principalOccurrenceOriginalOpen_isOpenImmersion e i k

/-- Each finite occurrence image has exactly its original image as inverse image. -/
theorem principalOccurrenceOpenAt_preimage {j : κ}
    (i : ι) (k : J i) (h : dst i k = j) :
    principalOccurrenceAmbientProjection e x i ⁻¹ᵁ
        (principalOccurrenceOpenAt e x hx i k h).opensRange =
      (principalOccurrenceOriginalOpenAt e i k h).opensRange := by
  subst j
  have H := principalOccurrenceOriginalOpen_isPullback e x hx i k
  simpa only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange,
    principalOccurrenceOpenAt, principalOccurrenceOriginalOpenAt] using
    (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback H ⊤).symm

/-- The entire original union is recovered by base change along the ambient projection. -/
theorem principalOccurrenceAmbientUnion_preimage {μ : Type*}
    (j : μ → κ) (i : ι) (k : μ → J i) (hk : ∀ m, dst i (k m) = j m) :
    principalOccurrenceAmbientProjection e x i ⁻¹ᵁ
        openImageUnion (fun m ↦ principalOccurrenceOpenAt e x hx i (k m) (hk m)) =
      openImageUnion (fun m ↦ principalOccurrenceOriginalOpenAt e i (k m) (hk m)) := by
  simp only [openImageUnion, Scheme.Hom.preimage_iSup, principalOccurrenceOpenAt_preimage]

end FLT.Mazur.FiniteTypeRelationModel
