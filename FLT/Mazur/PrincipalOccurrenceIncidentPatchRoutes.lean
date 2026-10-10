/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceTargetChartIncident

/-!
# Comparing incident chart routes on entire double overlaps

A literal target occurrence supplies a diagonal patch in the constrained
cover. Thus the exhaustive atlas comparisons identify both routes on each
whole double-open patch, without requiring equality of its outer labels.
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

/-- A literal incident target gives a covering constrained family at every bijective stage. -/
theorem principalOccurrenceIncidentPatchTo_cover (i : ι) (k : J i) :
    (⨆ p : PrincipalOccurrencePatchTo (dst := dst) (dst i k) i,
      (principalOccurrencePatchOpen x hx p.1).opensRange) = ⊤ := by
  apply top_unique
  intro z _
  let p : PrincipalOccurrencePatchTo (dst := dst) (dst i k) i :=
    ⟨⟨⟨⟨i, k⟩, rfl⟩, k⟩, ⟨k, rfl⟩⟩
  apply TopologicalSpace.Opens.mem_iSup.mpr
  exact ⟨p, (principalOccurrencePatchOpen x hx p.1).homeomorph.surjective z⟩

variable {j : κ} (i : ι) (k : J i) (hk : dst i k = j)
  (he : ∀ p q : PrincipalOccurrencePatchTo (dst := dst) j i,
    principalOccurrenceCrossOuterLeft x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i p.2.val p.2.property =
      principalOccurrenceCrossOuterRight x hx p.1 q.1 ≫
        principalOccurrenceOpenAt e x hx i q.2.val q.2.property)

include he in
/-- Comparison equations identify both target routes on the entire chosen patch. -/
@[reassoc] theorem principalOccurrencePatch_incident_route
    (p : PrincipalOccurrencePatchTo (dst := dst) j i) :
    principalOccurrencePatchOpen x hx p.1 ≫ principalOccurrenceOpenAt e x hx i k hk =
      principalOccurrenceTargetPatchMap e x hx i p := by
  subst j
  have hc := principalOccurrenceIncidentPatchTo_cover e x hx i k
  rw [← principalOccurrenceTargetChartGlue_eq_open e x hx i hc he k rfl]
  exact principalOccurrenceTargetChartGlue_fac e x hx i hc he p

include he in
/-- The two ambient routes agree on the actual pullback of two incoming occurrences. -/
theorem principalOccurrence_ambient_routes (i₀ : ι) (k₀ l₀ : J i₀)
    (h₀ : dst i₀ k₀ = j) (l : J i) (hl : dst i l = dst i₀ l₀) :
    pullback.fst (principalOccurrenceOpen x hx i₀ k₀)
        (principalOccurrenceOpen x hx i₀ l₀) ≫
        principalOccurrenceOpenAt e x hx i k (hk.trans h₀.symm) =
      pullback.snd (principalOccurrenceOpen x hx i₀ k₀)
        (principalOccurrenceOpen x hx i₀ l₀) ≫ principalOccurrenceOpenAt e x hx i l hl := by
  cases h₀
  have H := principalOccurrencePatch_isPullback x hx i₀ k₀ l₀
  apply (cancel_epi H.isoPullback.hom).mp
  simp only [H.isoPullback_hom_fst_assoc, H.isoPullback_hom_snd_assoc]
  exact principalOccurrencePatch_incident_route e x hx i k hk he
    ⟨⟨⟨⟨i₀, k₀⟩, rfl⟩, l₀⟩, ⟨l, hl⟩⟩

end FLT.Mazur.FiniteTypeRelationModel
