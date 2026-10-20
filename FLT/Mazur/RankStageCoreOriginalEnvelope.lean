/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentCoreCoverage
public import FLT.Mazur.RankStageTransitionTopology

/-!
# One original open inducing every coherent rank core

The zero-order core extends to an open of the unchanged source. Surjectivity
of all order transitions proves that this same open induces every higher core.
This gives original principal neighborhoods, without making the rank stages flat.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance envelopeOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance envelopeOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance envelopeOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)

omit [QuasiCompact p] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p] in
/-- The rank map has the induced topology from the unchanged original source. -/
theorem rankThickeningMap_isEmbedding (k : ℕ) :
    Topology.IsEmbedding (rankThickeningMap (Over.mk p) n k) := by
  exact (rankImageOpen (Over.mk p) n).ι.isEmbedding.comp
    (rankStratumIdeal (Over.mk p) n ^ (k + 1)).subschemeι.isClosedEmbedding.isEmbedding

/-- One original open induces the entire coordinated family, including every higher order. -/
theorem exists_rankStage_core_original_open :
    ∃ O : A.Opens, O ≤ rankImageOpen (Over.mk p) n ∧ ∀ k : ℕ,
      rankThickeningMap (Over.mk p) n k ⁻¹ᵁ O = rankStageCore e n a ha k := by
  obtain ⟨s, hs, he⟩ := (rankThickeningMap_isEmbedding (p := p) n 0).isInducing.isOpen_iff.mp
    (rankStageCore e n a ha 0).isOpen
  let O : A.Opens := ⟨s, hs⟩ ⊓ rankImageOpen (Over.mk p) n
  have hzero : rankThickeningMap (Over.mk p) n 0 ⁻¹ᵁ O = rankStageCore e n a ha 0 := by
    ext x
    have hx : rankThickeningMap (Over.mk p) n 0 x ∈ rankImageOpen (Over.mk p) n :=
      ((rankThickeningMap_range (Over.mk p) n 0).le ⟨x, rfl⟩).1
    change (rankThickeningMap (Over.mk p) n 0 x ∈ s ∧
      rankThickeningMap (Over.mk p) n 0 x ∈ rankImageOpen (Over.mk p) n) ↔ _
    exact (and_iff_left hx).trans (Set.ext_iff.mp he x)
  refine ⟨O, inf_le_right, fun k ↦ ?_⟩
  ext y
  obtain ⟨x, rfl⟩ := rankStageTransition_surjective (p := p) n (Nat.zero_le k) y
  have hm := congrArg (fun g ↦ g x)
    (rankStageTransition_map (Over.mk p) n (Nat.zero_le k))
  have hc := SetLike.ext_iff.mp (rankStageCore_preimage e n a ha (Nat.zero_le k)) x
  change rankThickeningMap (Over.mk p) n k
    (rankStageTransition (Over.mk p) n (Nat.zero_le k) x) ∈ O ↔ _
  change rankThickeningMap (Over.mk p) n k
    (rankStageTransition (Over.mk p) n (Nat.zero_le k) x) = _ at hm
  rw [hm]
  exact (SetLike.ext_iff.mp hzero x).trans hc.symm

/-- A point of the core has one original principal neighborhood valid at every order. -/
theorem exists_rankStage_core_original_principal
    (y : rankThickening (Over.mk p) n 0) (hy : y ∈ rankStageCore e n a ha 0) :
    ∃ b : Γ(A, ⊤), rankThickeningMap (Over.mk p) n 0 y ∈ A.basicOpen b ∧
      A.basicOpen b ≤ rankImageOpen (Over.mk p) n ∧ ∀ k : ℕ,
        rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤ rankStageCore e n a ha k := by
  obtain ⟨O, hO, hcores⟩ := exists_rankStage_core_original_open e n a ha
  have hyO : rankThickeningMap (Over.mk p) n 0 y ∈ O := by
    change y ∈ rankThickeningMap (Over.mk p) n 0 ⁻¹ᵁ O
    rwa [hcores]
  obtain ⟨b, hb, hbO⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal O
    {rankThickeningMap (Over.mk p) n 0 y} (Set.finite_singleton _) (by simpa using hyO)
  refine ⟨b, hb (Set.mem_singleton _), hbO.trans hO, fun k ↦ ?_⟩
  rw [← hcores k]
  exact (TopologicalSpace.Opens.map (rankThickeningMap (Over.mk p) n k).base).monotone hbO

end FLT.Mazur.EquivalenceRelationOrderedFrames
