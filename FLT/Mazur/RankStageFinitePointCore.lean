/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoherentCoreCoverage
public import FLT.Mazur.RankStageOriginalBoundaryCoefficients

/-!
# A common coherent core for finitely many points of one exact rank

Prime avoidance is applied to the union of the complete finite orbits.
The resulting single original parameter works at every thickening order.
No relation arrow between the selected points is assumed.
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
local instance pointCoreOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance pointCoreOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance pointCoreOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance pointCoreFirst_finite (n k : ℕ) : IsFinite (rankStageFirst (p := p) n k) :=
  rankStageFirst_finite n k

/-- All points of a finite family of one rank lie in one core at every order. -/
theorem exists_rankStage_finite_point_core {ι : Type} [Finite ι] (n : ℕ)
    (x : ι → A) (hx : ∀ i, x i ∈ exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k i, x i ∈ Set.range (rankStageCoreOriginalMap e n a ha k) := by
  have hy : ∀ i, ∃ y : rankThickening (Over.mk p) n 0,
      rankThickeningMap (Over.mk p) n 0 y = x i := by
    intro i
    have hi := hx i
    rwa [← rankThickeningMap_range (Over.mk p) n 0] at hi
  choose y hy using hy
  let r := rankStageFirst (p := p) n 0
  let s := rankStageSecond e n 0
  let b := rankThickeningMap (Over.mk p) n 0
  have hf (i : ι) : (r ⁻¹' {y i}).Finite :=
    SchemeOpenEnvelope.finite_fiber_of_mem_finiteTarget r (y i) (by
      rw [SchemeOpenEnvelope.finiteTargetOpen_eq_top r]
      trivial)
  let Z : Set A := ⋃ i, b '' (s '' (r ⁻¹' {y i}))
  have hZ : Z.Finite := Set.finite_iUnion fun i ↦ ((hf i).image s).image b
  obtain ⟨a, ha, haU⟩ := AffineEnvelopeFiniteNeighborhood.exists_envelope_principal
    (rankImageOpen (Over.mk p) n) Z hZ (by
      intro z hz
      obtain ⟨i, z, _, rfl⟩ := Set.mem_iUnion.mp hz
      exact ((rankThickeningMap_range (Over.mk p) n 0).le ⟨z, rfl⟩).1)
  have hc (i : ι) : y i ∈ rankStageCore e n a haU 0 := by
    apply (mem_core_iff (rankStageEquivalence e n 0) _ _ (y i)).mpr
    intro z hz
    rw [← Scheme.preimage_basicOpen_top]
    exact ha (Set.mem_iUnion.mpr ⟨i, s z, ⟨z, hz, rfl⟩, rfl⟩)
  refine ⟨a, haU, fun k i ↦ ?_⟩
  let z := rankStageTransition (Over.mk p) n (Nat.zero_le k) (y i)
  have hz : z ∈ rankStageCore e n a haU k := by
    change y i ∈ rankStageTransition (Over.mk p) n (Nat.zero_le k) ⁻¹ᵁ
      rankStageCore e n a haU k
    rw [rankStageCore_preimage]
    exact hc i
  refine ⟨⟨z, hz⟩, ?_⟩
  change (rankStageTransition (Over.mk p) n (Nat.zero_le k) ≫
    rankThickeningMap (Over.mk p) n k) (y i) = x i
  rw [rankStageTransition_map]
  exact hy i

end FLT.Mazur.EquivalenceRelationOrderedFrames
