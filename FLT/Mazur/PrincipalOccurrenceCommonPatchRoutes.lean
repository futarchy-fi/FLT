/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCommonUnion
/-!
# Actual triple-patch routes into canonical symmetric unions

A descended finite cover of a proper patch supplies its image inclusion in
the second-to-third common union. The route is an open immersion retaining
the original ambient map, with no full-domain cover assumption.
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

/-- An explicitly labeled finite patch cuts out the inverse image of its outer occurrence. -/
theorem principalOccurrencePatchOpenAt_image {j : κ} (i : ι) (k l : J i)
    (hk : dst i k = j) :
    (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l⟩).opensRange =
      principalOccurrenceOpenAt e x hx i k hk ⁻¹ᵁ (principalOccurrenceOpen x hx i l).opensRange :=
    by
  subst j
  let H := principalOccurrencePatch_isPullback x hx i k l
  have h := Scheme.Hom.opensRange_comp_of_isIso H.isoPullback.hom
    (pullback.fst (principalOccurrenceOpen x hx i k) (principalOccurrenceOpen x hx i l))
  simpa only [H.isoPullback_hom_fst, Scheme.Hom.opensRange_pullbackFst,
    principalOccurrenceOpenAt] using h

/-- A patch with an outer occurrence in another chart lands in the canonical common union. -/
theorem principalOccurrencePatch_common_image_le {j : κ}
    (i t : ι) (k l : J i) (hk : dst i k = j) (n : J t) (hn : dst t n = dst i l) :
    (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l⟩).opensRange ≤
      principalOccurrenceOpenAt e x hx i k hk ⁻¹ᵁ principalOccurrenceCommonUnion e x hx i t := by
  rw [principalOccurrencePatchOpenAt_image]
  intro z hz
  have h : (principalOccurrenceOpen x hx i l).opensRange ≤
      principalOccurrenceCommonUnion e x hx i t :=
    le_iSup_of_le (⟨dst i l, ⟨l, rfl⟩, ⟨n, hn⟩⟩ : PrincipalOccurrenceCommon dst i t) le_rfl
  exact h hz

variable {j : κ} (p : PrincipalOccurrencePatch (dst := dst) j)
  (i t : ι) (k : J i) (hk : dst i k = j)
  {μ : Type*} (l : μ → J i) (n : μ → J t) (hn : ∀ m, dst t (n m) = dst i (l m))
  (hc : (principalOccurrencePatchOpen x hx p).opensRange ≤
    ⨆ m, (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, hk⟩, l m⟩).opensRange)

include hc hn in
/-- Covering a proper patch by incident pair routes gives the entire required image inclusion. -/
theorem principalOccurrenceCoveredPatch_common_image_le :
    (principalOccurrencePatchOpen x hx p).opensRange ≤
      principalOccurrenceOpenAt e x hx i k hk ⁻¹ᵁ principalOccurrenceCommonUnion e x hx i t :=
  hc.trans (iSup_le fun m ↦ principalOccurrencePatch_common_image_le e x hx
    i t k (l m) hk (n m) (hn m))

/-- A covered triple patch has an actual map into the canonical second-to-third union. -/
def principalOccurrenceCommonPatchRoute :
    principalOccurrencePatchScheme x p ⟶ (principalOccurrenceCommonUnion e x hx i t).toScheme :=
  IsOpenImmersion.lift (principalOccurrenceCommonUnion e x hx i t).ι
    (principalOccurrencePatchOpen x hx p ≫ principalOccurrenceOpenAt e x hx i k hk) (by
      change (principalOccurrencePatchOpen x hx p ≫
        principalOccurrenceOpenAt e x hx i k hk).opensRange ≤
          (principalOccurrenceCommonUnion e x hx i t).ι.opensRange
      rw [Scheme.Opens.opensRange_ι]
      rintro z ⟨w, rfl⟩
      exact principalOccurrenceCoveredPatch_common_image_le e x hx p i t k hk l n hn hc
        ⟨w, rfl⟩)

/-- The constructed triple route retains its actual map to the second ambient chart. -/
@[reassoc] theorem principalOccurrenceCommonPatchRoute_fac :
    principalOccurrenceCommonPatchRoute e x hx p i t k hk l n hn hc ≫
        (principalOccurrenceCommonUnion e x hx i t).ι =
      principalOccurrencePatchOpen x hx p ≫ principalOccurrenceOpenAt e x hx i k hk :=
  IsOpenImmersion.lift_fac _ _ _

/-- Every constructed triple route is an open immersion. -/
instance principalOccurrenceCommonPatchRoute_isOpenImmersion :
    IsOpenImmersion (principalOccurrenceCommonPatchRoute e x hx p i t k hk l n hn hc) := by
  dsimp only [principalOccurrenceCommonPatchRoute]
  infer_instance

end FLT.Mazur.FiniteTypeRelationModel
