/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreOriginalEnvelope
public import FLT.Mazur.SchemeFiniteTargetFiber

/-!
# One coherent affine core around a finite original rank locus

The union of all relation fibers over a finite set is finite. Prime avoidance
therefore chooses one original parameter whose invariant core contains every
point of that set at every order. The parameter is shared before any lift is chosen.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples FiniteRelationAffinePrincipalCore
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance finiteCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance finiteCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance finiteCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance finiteCoreFirst_finite (n k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k

/-- A finite set at order zero fits in one core at every infinitesimal order. -/
theorem exists_rankStage_core_finite_set (n : ℕ)
    (s : Set (rankThickening (Over.mk p) n 0)) (hs : s.Finite) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k : ℕ, rankStageTransition (Over.mk p) n (Nat.zero_le k) '' s ⊆
        rankStageCore e n a ha k := by
  let r := rankStageFirst (p := p) n 0
  let q' := rankStageSecond e n 0
  let b := rankThickeningMap (Over.mk p) n 0
  have hf : (r ⁻¹' s).Finite := by
    have h : (⋃ y ∈ s, r ⁻¹' {y}).Finite := hs.biUnion fun y _ ↦
      SchemeOpenEnvelope.finite_fiber_of_mem_finiteTarget r y (by
        rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top r]
        trivial)
    exact h.subset fun z hz ↦ Set.mem_iUnion₂.mpr ⟨r z, hz, rfl⟩
  obtain ⟨a, ha, haU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (rankImageOpen (Over.mk p) n) (b '' (q' '' (r ⁻¹' s))) ((hf.image q').image b) (by
      rintro _ ⟨z, _, rfl⟩
      exact ((rankThickeningMap_range (Over.mk p) n 0).le ⟨z, rfl⟩).1)
  have hc : s ⊆ rankStageCore e n a haU 0 := by
    intro y hy
    apply (mem_core_iff (rankStageEquivalence e n 0) _ _ y).mpr
    intro z hz
    rw [← Scheme.preimage_basicOpen_top]
    exact ha ⟨q' z, ⟨z, by change r z ∈ s; rwa [hz], rfl⟩, rfl⟩
  refine ⟨a, haU, fun k ↦ ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  change y ∈ rankStageTransition (Over.mk p) n (Nat.zero_le k) ⁻¹ᵁ
    rankStageCore e n a haU k
  rw [rankStageCore_preimage]
  exact hc hy

/-- A finite subset of the unchanged exact-rank locus has one shared original neighborhood. -/
theorem exists_rankStage_original_finite_neighborhood (n : ℕ)
    (s : Set A) (hs : s.Finite) (hsn : s ⊆ exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (b : Γ(A, ⊤)), s ⊆ A.basicOpen b ∧
      A.basicOpen b ≤ rankImageOpen (Over.mk p) n ∧ ∀ k : ℕ,
        rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ rankStageCore e n a ha k := by
  let f := rankThickeningMap (Over.mk p) n 0
  have hf : (f ⁻¹' s).Finite := hs.preimage (rankThickeningMap_isEmbedding n 0).injective.injOn
  obtain ⟨a, ha, hc⟩ := exists_rankStage_core_finite_set e n (f ⁻¹' s) hf
  obtain ⟨O, hO, hcores⟩ := exists_rankStage_core_original_open e n a ha
  have hsO : s ⊆ O := by
    intro x hx
    obtain ⟨y, hy⟩ := (rankThickeningMap_range (Over.mk p) n 0).symm.le (hsn hx)
    have hys : y ∈ f ⁻¹' s := by
      change f y ∈ s
      rwa [hy]
    have hyc := hc 0 (Set.mem_image_of_mem _ hys)
    have he : rankStageTransition (Over.mk p) n (Nat.zero_le 0) y = y := by
      apply (rankThickeningMap_isEmbedding n 0).injective
      exact congrArg (fun g ↦ g y) (rankStageTransition_map (Over.mk p) n (Nat.zero_le 0))
    rw [he, ← hcores 0] at hyc
    change f y ∈ O at hyc
    rwa [hy] at hyc
  obtain ⟨b, hb, hbO⟩ :=
    AffineEnvelopeFiniteNeighborhood.exists_envelope_principal O s hs hsO
  refine ⟨a, ha, b, hb, hbO.trans hO, fun k ↦ ?_⟩
  rw [← hcores k]
  exact (TopologicalSpace.Opens.map (rankThickeningMap (Over.mk p) n k).base).monotone hbO

end FLT.Mazur.EquivalenceRelationOrderedFrames
