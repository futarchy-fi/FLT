/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteExactRank
public import FLT.Mazur.EquivalenceRelationRankStratumCover
public import FLT.Mazur.EquivalenceRelationCompleteInteriorFinite
public import FLT.Mazur.RelativeFrameDenseRankStrata

/-!
# Exact rank description of the original finite locus

The maximal complete open is exactly the inverse image of the original open
rank bound. Consequently the union of open rank strata is the whole finite
target locus, and not just a dense subset of it. No closed stratum replaces
an open neighborhood in the original source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance exactInteriorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance exactInteriorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance exactInteriorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- Interior completeness is precisely exclusion of approaching larger original frames. -/
theorem completeInterior_eq_rankBound_preimage (n : ℕ) (o : Fin n) :
    completeInterior (p := p) (q := q) (Fin n) o =
      first p q (Fin n) o ⁻¹ᵁ rankBoundOpen (Over.mk p) n := by
  let _ := first_etale e (Fin n) o
  apply TopologicalSpace.Opens.ext
  change interior (completePointLocus (p := p) (q := q) (Fin n) o) = _
  rw [completePointLocus_eq_rankAtMost_preimage]
  rw [← (first p q (Fin n) o).isOpenMap.preimage_interior_eq_interior_preimage
    (first p q (Fin n) o).continuous]
  change first p q (Fin n) o ⁻¹' interior (Set.range
    (distinctScheme (Over.mk p) (Fin (n + 1))).hom)ᶜ = _
  rw [interior_compl]
  rfl

include e in
/-- An interior complete n-frame lands in the original open exact n-rank stratum. -/
theorem completeInterior_endpoint_rankStratum (n : ℕ) (o : Fin n)
    (x : source p q (Fin n) o)
    (hx : x ∈ completeInterior (p := p) (q := q) (Fin n) o) :
    first p q (Fin n) o x ∈ rankStratumOpen (Over.mk p) n := by
  rw [completeInterior_eq_rankBound_preimage e] at hx
  exact ⟨⟨inclusion p q (Fin n) o x, rfl⟩, hx⟩

variable [LocallyQuasiFinite p]

include e in
/-- The entire original finite target locus is exactly the union of the open rank strata. -/
theorem finiteTargetOpen_eq_rankStrataOpen :
    finiteTargetOpen p = rankStrataOpen (Over.mk p) := by
  ext x
  change x ∈ finiteTargetOpen p ↔ x ∈ rankStrataOpen (Over.mk p)
  rw [finiteTarget_iff_exists_completeInterior e]
  change (∃ (n : ℕ) (o : Fin n) (y : source p q (Fin n) o),
    first p q (Fin n) o y = x ∧ y ∈ completeInterior (Fin n) o) ↔
      x ∈ ⨆ n : ℕ, rankStratumOpen (Over.mk p) n
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨n, o, y, hy, hc⟩
    exact ⟨n, hy ▸ completeInterior_endpoint_rankStratum e n o y hc⟩
  · rintro ⟨n, hn⟩
    obtain ⟨o, y, hy, hc⟩ := exists_rankStratum_interior_lift e n x hn
    exact ⟨n, o, y, hy, hc⟩

include e in
/-- At its exact original rank, local finiteness is equivalent to exclusion of rank jumps. -/
theorem finiteTarget_iff_rankBound_of_exactRank (n : ℕ) (x : A)
    (hx : x ∈ exactRank (Over.mk p) n) :
    x ∈ finiteTargetOpen p ↔ x ∈ rankBoundOpen (Over.mk p) n := by
  rw [finiteTargetOpen_eq_rankStrataOpen e]
  change x ∈ ⨆ m : ℕ, rankStratumOpen (Over.mk p) m ↔ _
  rw [TopologicalSpace.Opens.mem_iSup]
  constructor
  · rintro ⟨m, hm⟩
    have he : m = n := by
      by_contra h
      exact Set.disjoint_left.mp (exactRank_disjoint (Over.mk p) h)
        ⟨hm.1, rankBoundOpen_no_larger (Over.mk p) m hm.2⟩ hx
    exact he ▸ hm.2
  · intro hb
    exact ⟨n, hx.1, hb⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
