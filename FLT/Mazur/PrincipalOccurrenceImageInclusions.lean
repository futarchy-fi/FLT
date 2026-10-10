/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCartesian
public import FLT.Mazur.PrincipalOccurrenceCofinalBijections
public import FLT.Mazur.FiniteRelationLocalizedInclusionDescent

/-!
# Simultaneous descent of actual patch image inclusions

Original geometric inclusions become basic-open inclusions in the canonical
localized quotient. Their finite power certificates descend simultaneously
to a bijective occurrence stage and persist under every later refinement.
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

/-- Original patch image inclusion holds in the canonical quotient coordinates. -/
theorem principalOccurrencePatchInclusion_quotient {j : κ}
    (p q : PrincipalOccurrencePatch (dst := dst) j)
    (h : (principalOccurrenceOriginalPatchOpen e p).opensRange ≤
      (principalOccurrenceOriginalPatchOpen e q).opensRange) :
    PrimeSpectrum.basicOpen (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalOccurrencePatchDenominator x p)) ≤
      PrimeSpectrum.basicOpen (FiniteRelationLocalization.toQuotient R (relationIdeal R (B j))
        (principalRepresentative R (B j) (b j)) (x.target j)
        (principalOccurrencePatchDenominator x q)) := by
  intro z hz
  let z' := PrimeSpectrum.comap (principalQuotientEquiv R (B j) (b j)).symm.toRingHom z
  have hp : z' ∈ (principalOccurrenceOriginalPatchOpen e p).opensRange := by
    rw [principalOccurrenceOriginalPatch_opensRange]
    change ¬ (principalQuotientEquiv R (B j) (b j)).symm
      (principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) p) ∈
        z.asIdeal
    rw [← principalOccurrencePatchDenominator_recovery x p]
    change ¬ (principalQuotientEquiv R (B j) (b j)).symm
      (principalQuotientEquiv R (B j) (b j) _) ∈ z.asIdeal
    rw [AlgEquiv.symm_apply_apply]
    exact hz
  have hq := h hp
  rw [principalOccurrenceOriginalPatch_opensRange] at hq
  change ¬ (principalQuotientEquiv R (B j) (b j)).symm
    (principalOccurrenceOriginalPatchDenominator (f := fun i k ↦ (e i k).toAlgHom) q) ∈
      z.asIdeal at hq
  rw [← principalOccurrencePatchDenominator_recovery x q] at hq
  change ¬ (principalQuotientEquiv R (B j) (b j)).symm
    (principalQuotientEquiv R (B j) (b j) _) ∈ z.asIdeal at hq
  rw [AlgEquiv.symm_apply_apply] at hq
  exact hq

variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]

/-- A finite family of original image inclusions holds at every stage above one refinement. -/
theorem exists_principalOccurrence_patch_inclusions {ν : κ → Type*} [∀ j, Finite (ν j)]
    (p q : ∀ j, ν j → PrincipalOccurrencePatch (dst := dst) j)
    (h : ∀ j n, (principalOccurrenceOriginalPatchOpen e (p j n)).opensRange ≤
      (principalOccurrenceOriginalPatchOpen e (q j n)).opensRange)
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧ (∀ i k, Function.Bijective (y.hom i k)) ∧
        ∀ z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom), y ≤ z →
          ∀ hz : ∀ i k, Function.Bijective (z.hom i k), ∀ j n,
            (principalOccurrencePatchOpen z hz (p j n)).opensRange ≤
              (principalOccurrencePatchOpen z hz (q j n)).opensRange := by
  choose t hxt ht using fun j ↦
    FiniteRelationLocalization.exists_localized_principal_inclusions_tail
      (relationIdeal R (B j)) (principalRepresentative R (B j) (b j)) (x.target j)
      (fun n ↦ principalOccurrencePatchDenominator x (p j n))
      (fun n ↦ principalOccurrencePatchDenominator x (q j n))
      (fun n ↦ principalOccurrencePatchInclusion_quotient e x (p j n) (q j n) (h j n))
  obtain ⟨y, hxy, hs, hty, hy⟩ := exists_principalOccurrence_bijective_refinement e x s t
  refine ⟨y, hxy, hs, hy, fun z hyz hz j n ↦ ?_⟩
  have htz := (hty j).trans (principalOccurrence_target_mono hyz j)
  simp_rw [principalOccurrencePatch_opensRange,
    ← principalOccurrencePatchDenominator_transition (hxy.trans hyz)]
  exact ht j (z.target j) htz n

end FLT.Mazur.FiniteTypeRelationModel
