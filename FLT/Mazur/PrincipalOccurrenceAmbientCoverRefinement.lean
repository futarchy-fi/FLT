/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceOriginalCartesian
public import FLT.Mazur.PrincipalOccurrenceCofinalBijections
public import FLT.Mazur.FiniteRelationPrincipalCoverModels

/-!
# Persistent ambient chart covers at finite occurrence stages

The original occurrence cover descends through the finite relation models.
Consequently the diagonal common union can become the whole finite chart.
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




variable [∀ i, Algebra.FiniteType R (A i)] [∀ j, Algebra.FiniteType R (B j)]
  (x : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))

omit [∀ j, Algebra.FiniteType R (B j)] in
/-- An original ambient occurrence cover is a cover of the full presentation quotient. -/
theorem principalOccurrenceAmbientCover_quotient (i : ι)
    (hc : (⨆ k, (principalOccurrenceOriginalOpen e i k).opensRange) = ⊤) :
    (⨆ k, PrimeSpectrum.basicOpen
      (Ideal.Quotient.mk (relationIdeal R (A i))
        (principalRepresentative R (A i) (a i k)))) = ⊤ := by
  apply top_unique
  intro z _
  let z' := PrimeSpectrum.comap (quotientEquiv R (A i)).symm.toRingHom z
  have hz : z' ∈ ⨆ k, (principalOccurrenceOriginalOpen e i k).opensRange := by
    rw [hc]
    trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨k, ?_⟩
  rw [principalOccurrenceOriginalOpen_opensRange] at hk
  change ¬ (quotientEquiv R (A i)).symm (a i k) ∈ z.asIdeal at hk
  have hrep : (quotientEquiv R (A i)).symm (a i k) =
      Ideal.Quotient.mk (relationIdeal R (A i))
        (principalRepresentative R (A i) (a i k)) := by
    apply (quotientEquiv R (A i)).injective
    rw [AlgEquiv.apply_symm_apply]
    exact (principalRepresentative_spec R (A i) (a i k)).symm
  rw [hrep] at hk
  exact hk

variable [Finite ι] [Finite κ] [∀ i, Finite (J i)]

/-- Original chart covers descend to one bijective stage and every later bijective stage. -/
theorem exists_principalOccurrence_ambient_covers
    (hc : ∀ i, (⨆ k, (principalOccurrenceOriginalOpen e i k).opensRange) = ⊤)
    (s : ∀ i, Finset (relationIdeal R (A i))) :
    ∃ y : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom),
      ∃ _hxy : x ≤ y, s ≤ y.source ∧
        ∃ _hy : ∀ i k, Function.Bijective (y.hom i k),
          ∀ (z : PrincipalOccurrenceStage dst a b (fun i k ↦ (e i k).toAlgHom))
            (_hyz : y ≤ z) (hz : ∀ i k, Function.Bijective (z.hom i k)) (i : ι),
            (⨆ k, (principalOccurrenceOpen z hz i k).opensRange) = ⊤ := by
  choose t hst ht using fun i ↦
    FiniteRelationLocalization.exists_principal_cover_tail (relationIdeal R (A i))
      (fun k ↦ principalRepresentative R (A i) (a i k)) (s i)
      (principalOccurrenceAmbientCover_quotient e i (hc i))
  obtain ⟨y, hxy, hty, _, hy⟩ :=
    exists_principalOccurrence_bijective_refinement e x t x.target
  refine ⟨y, hxy, fun i ↦ (hst i).trans (hty i), hy, fun z hyz hz i ↦ ?_⟩
  simp_rw [principalOccurrenceOpen_opensRange]
  exact ht i (z.source i) ((hty i).trans (principalOccurrence_source_mono hyz i))

end FLT.Mazur.FiniteTypeRelationModel
