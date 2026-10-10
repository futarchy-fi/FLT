/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCartesian
public import FLT.Mazur.PrincipalOccurrenceCofinalBijections
public import FLT.Mazur.FiniteRelationLocalizedCoverDescent

/-!
# Simultaneous finite patch covers at bijective occurrence stages

Any prescribed finite patch subfamilies that cover the original overlaps
cover at one bijective refinement. This applies to constrained subfamilies;
it does not insert diagonal patches to make the cover condition automatic.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

attribute [local irreducible] principalQuotientEquiv FiniteRelationLocalization.toQuotient

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  (e : ∀ i k, Localization.Away (a i k) ≃ₐ[R] Localization.Away (b (dst i k)))




variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

/-- An original patch cover is a principal cover in the canonical overlap quotient. -/
theorem principalOccurrencePatchCover_quotient {j : κ} {ν : Type*}
    (p : ν → PrincipalOccurrencePatch (dst := dst) j)
    (hp : (⨆ n, (principalOccurrenceOriginalPatchOpen e (p n)).opensRange) = ⊤) :
    (⨆ n, PrimeSpectrum.basicOpen
      (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalOccurrencePatchDenominator x (p n)))) = ⊤ := by
  apply le_antisymm le_top
  intro z _
  let z' := PrimeSpectrum.comap (principalQuotientEquiv R (B j) (b j)).symm.toRingHom z
  have hz : z' ∈ ⨆ n, (principalOccurrenceOriginalPatchOpen e (p n)).opensRange := by
    rw [hp]
    trivial
  obtain ⟨n, hn⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨n, ?_⟩
  rw [principalOccurrenceOriginalPatch_opensRange] at hn
  change ¬ (principalQuotientEquiv R (B j) (b j)).symm
    (principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) (p n)) ∈
      z.asIdeal at hn
  rw [← principalOccurrencePatchDenominator_recovery x (p n)] at hn
  change ¬ (principalQuotientEquiv R (B j) (b j)).symm
    (principalQuotientEquiv R (B j) (b j) _) ∈ z.asIdeal at hn
  rw [AlgEquiv.symm_apply_apply] at hn
  exact hn

variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]

/-- Prescribed finite original patch covers hold at one common bijective occurrence refinement. -/
theorem exists_principalOccurrence_patch_covers {ν : κ → Type*} [∀ j, Finite (ν j)]
    (p : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
    (hp : ∀ j, (⨆ n, (principalOccurrenceOriginalPatchOpen e (p j n)).opensRange) = ⊤)
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ hy : ∀ i k, Function.Bijective (y.hom i k),
          ∀ j, (⨆ n, (principalOccurrencePatchOpen y hy (p j n)).opensRange) = ⊤ := by
  choose t hxt hcover using fun j ↦
    FiniteRelationLocalization.exists_localized_principal_cover_tail
      (relationIdeal R (B j)) (principalRepresentative R (B j) (b j)) (x.target j)
      (fun n ↦ principalOccurrencePatchDenominator x (p j n))
      (principalOccurrencePatchCover_quotient e x (p j) (hp j))
  obtain ⟨y, hxy, hs, ht, hy⟩ := exists_principalOccurrence_bijective_refinement e x s t
  refine ⟨y, hxy, hs, hy, fun j ↦ ?_⟩
  simp_rw [principalOccurrencePatch_opensRange,
    ← principalOccurrencePatchDenominator_transition hxy]
  exact hcover j (y.target j) (ht j)

end FLT.Mazur.FiniteTypeRelationModel
