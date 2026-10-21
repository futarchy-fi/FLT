/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFieldBoundaryPairs

/-!
# Exact-rank obstruction for original boundary arrows

Any original boundary arrow preserves the exact original rank. Consequently
its field endpoints have constructed common-core factors. Distinct exact ranks
cannot be repaired by passing to linked cores or to higher orders.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (e : CategoryTheory.EquivalenceRelation p q)
local instance arrowRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance arrowRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance arrowRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
  {K : Type} [Field K] (x y : Spec (.of K) ⟶ J.subscheme)

include e in
/-- A full boundary arrow preserves each exact original rank on its prescribed endpoints. -/
theorem originalBoundary_field_arrow_rank_iff
    (d : Spec (.of K) ⟶ pullback p J.subschemeι)
    (hx : d ≫ pullback.snd p J.subschemeι = x)
    (hy : d ≫ InvariantIdealRelation.snd J p q hJ = y) (n : ℕ) :
    (x ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n ↔
      (y ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n := by
  rw [← hx, ← hy, Category.assoc, Category.assoc,
    ← pullback.condition, InvariantIdealRelation.snd_ι]
  exact exactRank_endpoint_iff e n ((d ≫ pullback.fst p J.subschemeι)
    (IsLocalRing.closedPoint K))

include e in
/-- Distinct exact ranks rule out any full original boundary arrow. -/
theorem originalBoundary_field_no_arrow_of_distinct_ranks {n m : ℕ} (hnm : n ≠ m)
    (hx : (x ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n)
    (hy : (y ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) m) :
    ¬ ∃ d : Spec (.of K) ⟶ pullback p J.subschemeι,
      d ≫ pullback.snd p J.subschemeι = x ∧ d ≫ InvariantIdealRelation.snd J p q hJ = y := by
  rintro ⟨d, hd, hd'⟩
  have hn := (originalBoundary_field_arrow_rank_iff e J hJ x y d hd hd' n).mp hx
  exact Set.disjoint_left.mp (exactRank_disjoint (Over.mk p) hnm) hn hy

variable [Etale q] [IsLocallyNoetherian A] [IsAffine A] [LocallyQuasiFinite p]

/-- An original arrow constructs common full boundary factors at all orders. -/
theorem originalBoundary_field_arrow_common_core
    (d : Spec (.of K) ⟶ pullback p J.subschemeι)
    (hx : d ≫ pullback.snd p J.subschemeι = x)
    (hy : d ≫ InvariantIdealRelation.snd J p q hJ = y) :
    ∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃ u v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = x ∧
        v ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = y := by
  obtain ⟨n, hn⟩ := exists_exactRank (Over.mk p)
    ((x ≫ J.subschemeι) (IsLocalRing.closedPoint K))
  obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_pair e J n x y hn
    ((originalBoundary_field_arrow_rank_iff e J hJ x y d hx hy n).mp hn)
  exact ⟨n, a, ha, hc⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
