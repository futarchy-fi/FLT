/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentAffineCores
public import FLT.Mazur.SchemeFiniteTargetFiber

/-!
# Coherent rank-stage affine towers through every original point

Prime avoidance chooses a single original affine parameter around the entire
rank-zero-order orbit. Its affine norm cores at every order contain compatible
lifts of the given original point. All domains retain the whole relation.
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
local instance coverageOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance coverageOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance coverageOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance coverageFirst_finite (n k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k

/-- Every original point lies under a single coordinated affine invariant tower. -/
theorem exists_rankStage_coherent_core (x : A) :
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (y : ∀ k : ℕ, rankThickening (Over.mk p) n k),
      (∀ k, rankThickeningMap (Over.mk p) n k (y k) = x) ∧
      (∀ k, y k ∈ rankStageCore e n a ha k) ∧
      ∀ k l (h : k ≤ l), rankStageTransition (Over.mk p) n h (y k) = y l := by
  obtain ⟨n, y, hy⟩ := exists_rankThickening_lift (Over.mk p) x 0
  let r := rankStageFirst (p := p) n 0
  let s := rankStageSecond e n 0
  let b := rankThickeningMap (Over.mk p) n 0
  have hf : (r ⁻¹' {y}).Finite :=
    SchemeOpenEnvelope.finite_fiber_of_mem_finiteTarget r y (by
      rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top r]
      trivial)
  obtain ⟨a, ha, haU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (rankImageOpen (Over.mk p) n) (b '' (s '' (r ⁻¹' {y}))) ((hf.image s).image b) (by
      rintro _ ⟨z, _, rfl⟩
      have hz : b z ∈ exactRank (Over.mk p) n :=
        (rankThickeningMap_range (Over.mk p) n 0).le ⟨z, rfl⟩
      exact hz.1)
  have hc : y ∈ rankStageCore e n a haU 0 := by
    apply (mem_core_iff (rankStageEquivalence e n 0) _ _ y).mpr
    intro z hz
    rw [← Scheme.preimage_basicOpen_top]
    exact ha ⟨s z, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨n, a, haU, fun k ↦ rankStageTransition (Over.mk p) n (Nat.zero_le k) y,
    ?_, ?_, ?_⟩
  · intro k
    change (rankStageTransition (Over.mk p) n (Nat.zero_le k) ≫
      rankThickeningMap (Over.mk p) n k) y = x
    rw [rankStageTransition_map]
    exact hy
  · intro k
    change y ∈ rankStageTransition (Over.mk p) n (Nat.zero_le k) ⁻¹ᵁ
      rankStageCore e n a haU k
    rw [rankStageCore_preimage]
    exact hc
  · intro k l h
    change (rankStageTransition (Over.mk p) n (Nat.zero_le k) ≫
      rankStageTransition (Over.mk p) n h) y = _
    rw [rankStageTransition_comp]

end FLT.Mazur.EquivalenceRelationOrderedFrames
