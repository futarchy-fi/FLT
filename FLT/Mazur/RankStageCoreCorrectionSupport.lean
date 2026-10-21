/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreCorrectionCriterion
public import FLT.Mazur.RankStageCoreCorrectionSpace
public import FLT.Mazur.HomogeneousCochainFinitePatching
public import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Original invariant neighborhoods for exact compatible core corrections

Away from the closed support of the actual correction class, one original
scalar constructs a homogeneous correction on every whole core. A support
inclusion gives a single exponent for all orders. These statements concern
the actual correction class, not stagewise or pairwise extension ideals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance supportCorrectionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance supportCorrectionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance supportCorrectionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] rankStageOriginalCoreAlgebra
variable (n : ℕ) {ι : Type*} (c : ι → Γ(A, ⊤))
  (hc : ∀ j, A.basicOpen (c j) ≤ rankImageOpen (Over.mk p) n) (J : A.IdealSheafData)
  (v : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j))
local notation "K" => rankStageCoreCorrectionIdeal e n c hc J v
attribute [local irreducible] rankStageCore rankStageCoreRestriction
  rankStageGlobalCoreRestriction rankStageInvariantTransition rankStageCoreCorrectionIdeal

/-- Every point off the genuine support has an unchanged original scalar and full corrections. -/
theorem exists_rankStage_core_corrections_away
    (x : PrimeSpectrum (compatibleFunctions p q)) (hx : x ∉ PrimeSpectrum.zeroLocus (K : Set _)) :
    ∃ (s : compatibleFunctions p q)
      (h : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)), s ∉ x.asIdeal ∧
      (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        ((h j).val k).val = 0) ∧
      ∀ i j k, rankStageInvariantOverlapError e n (c i) (c j) (hc i) (hc j) k
        (((s • v i) - h i).val k) (((s • v j) - h j).val k) = 0 := by
  have hex : ∃ s ∈ K, s ∉ x.asIdeal := by
    by_contra! h
    exact hx h
  obtain ⟨s, hs, hxs⟩ := hex
  obtain ⟨h, hh, he⟩ := (mem_rankStageCoreCorrectionIdeal e n c hc J v s).mp hs
  exact ⟨s, h, hxs, hh, he⟩

/-- Closed-support containment yields one exponent with ordinary all-order cochain corrections. -/
theorem exists_rankStage_core_corrections_of_support (Q : Ideal (compatibleFunctions p q))
    (hQ : PrimeSpectrum.zeroLocus (K : Set (compatibleFunctions p q)) ⊆
      PrimeSpectrum.zeroLocus (Q : Set (compatibleFunctions p q)))
    (s : compatibleFunctions p q) (hs : s ∈ Q) :
    ∃ (N : ℕ) (h : ∀ j, rankStageCompatibleCoreInvariants e n (c j) (hc j)),
      (∀ j k, (rankStageCoreBoundaryIdeal e n (c j) (hc j) J k).subschemeι.appTop
        ((h j).val k).val = 0) ∧
      ∀ i j k, rankStageInvariantOverlapError e n (c i) (c j) (hc i) (hc j) k
        (((s ^ N • v i) - h i).val k) (((s ^ N • v j) - h j).val k) = 0 := by
  have hr : s ∈ (K).radical :=
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hQ) hs
  obtain ⟨N, hN⟩ := Ideal.mem_radical_iff.mp hr
  obtain ⟨h, hh, he⟩ := (mem_rankStageCoreCorrectionIdeal e n c hc J v (s ^ N)).mp hN
  exact ⟨N, h, hh, he⟩

/-- A finite partition of one in original admissible scalars kills the actual correction class. -/
theorem rankStageCoreCorrectionObstruction_eq_zero_of_partition {κ : Type*} [Fintype κ]
    (s r : κ → compatibleFunctions p q) (hs : ∑ j, r j * s j = 1)
    (h : ∀ j, s j ∈ K) : rankStageCoreCorrectionObstruction e n c hc J v = 0 := by
  apply (one_mem_rankStageCoreCorrectionIdeal e n c hc J v).mp
  rw [← hs]
  exact (K).sum_mem (fun j _ ↦ (K).mul_mem_left (r j) (h j))

end FLT.Mazur.EquivalenceRelationOrderedFrames
