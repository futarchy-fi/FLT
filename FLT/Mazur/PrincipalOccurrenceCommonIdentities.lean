/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonUnion
/-!
# Symmetry and diagonal identities for common occurrence unions

Reversal is the actual inverse and a diagonal comparison is the identity.
The diagonal open contains every occurrence of its ambient chart.
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

/-- The diagonal union is exactly the union of all occurrences in that chart. -/
theorem principalOccurrenceCommonUnion_diagonal (i : ι) :
    principalOccurrenceCommonUnion e x hx i i =
      ⨆ k : J i, (principalOccurrenceOpen x hx i k).opensRange := by
  apply le_antisymm
  · apply iSup_le
    intro p
    obtain ⟨j, ⟨k, hk⟩, l⟩ := p
    subst j
    exact le_iSup (fun k ↦ (principalOccurrenceOpen x hx i k).opensRange) k
  · apply iSup_le
    intro k
    exact le_iSup_of_le (principalOccurrenceCommonDiagonal dst i k) le_rfl

variable
  (he : ∀ j (p q : PrincipalOccurrencePatch (dst := dst) j)
    (i : ι) (k l : J i)
    (hk : dst i k = dst p.1.val.1 p.2) (hl : dst i l = dst q.1.val.1 q.2),
    principalOccurrenceCrossOuterLeft x hx p q ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceCrossOuterRight x hx p q ≫ principalOccurrenceOpenAt e x hx i l hl)


/-- Canonical reverse comparisons are inverse on the full ambient union. -/
theorem principalOccurrenceCommonUnionIso_comp (i t : ι) :
    (principalOccurrenceCommonUnionIso e x hx he i t).hom ≫
        (principalOccurrenceCommonUnionIso e x hx he t i).hom = 𝟙 _ := by
  apply openImageUnion_hom_ext (principalOccurrenceCommonLeft e x hx i t)
  intro p
  exact (principalOccurrenceCommonUnionIso_fac_assoc e x hx he i t p _).trans
    ((principalOccurrenceCommonUnionIso_fac e x hx he t i
      (principalOccurrenceCommonSwap dst i t p)).trans (Category.comp_id _).symm)

/-- The canonical isomorphism for the reverse ordered pair is the inverse isomorphism. -/
theorem principalOccurrenceCommonUnionIso_reverse (i t : ι) :
    (principalOccurrenceCommonUnionIso e x hx he i t).symm =
      principalOccurrenceCommonUnionIso e x hx he t i := by
  apply Iso.ext
  apply (cancel_epi (principalOccurrenceCommonUnionIso e x hx he i t).hom).mp
  exact (Iso.hom_inv_id _).trans (principalOccurrenceCommonUnionIso_comp e x hx he i t).symm

include he in
/-- Two literal occurrences of the same overlap in one chart have identical embeddings. -/
theorem principalOccurrenceOpenAt_unique {j : κ} (i : ι) (k l : J i)
    (hk : dst i k = j) (hl : dst i l = j) :
    principalOccurrenceOpenAt e x hx i k hk = principalOccurrenceOpenAt e x hx i l hl := by
  have h := principalOccurrenceOpenAt_ambient_routes e x hx he i i k k k l hk hk hk hl
  have h' := congrArg (fun m ↦ pullback.diagonal
    (principalOccurrenceOpenAt e x hx i k hk) ≫ m) h
  simpa only [← Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd,
    Category.id_comp] using h'

/-- The diagonal comparison is the identity on the entire diagonal union. -/
theorem principalOccurrenceCommonUnionIso_diagonal (i : ι) :
    (principalOccurrenceCommonUnionIso e x hx he i i).hom = 𝟙 _ := by
  apply openImageUnion_hom_ext (principalOccurrenceCommonLeft e x hx i i)
  intro p
  have hmap : openImageUnionMap (principalOccurrenceCommonLeft e x hx i i)
      (principalOccurrenceCommonSwap dst i i p) =
      openImageUnionMap (principalOccurrenceCommonLeft e x hx i i) p := by
    apply (cancel_mono (openImageUnion (principalOccurrenceCommonLeft e x hx i i)).ι).mp
    exact (openImageUnionMap_fac (principalOccurrenceCommonLeft e x hx i i)
      (principalOccurrenceCommonSwap dst i i p)).trans
      ((principalOccurrenceOpenAt_unique e x hx he i p.2.2.val p.2.1.val
        p.2.2.property p.2.1.property).trans (openImageUnionMap_fac
          (principalOccurrenceCommonLeft e x hx i i) p).symm)
  exact (principalOccurrenceCommonUnionIso_fac e x hx he i i p).trans
    (hmap.trans (Category.comp_id _).symm)

end FLT.Mazur.FiniteTypeRelationModel
