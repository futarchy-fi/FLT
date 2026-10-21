/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageFieldBoundaryFamily

/-!
# Two original field endpoints on one full boundary tower

Equal exact ranks suffice to construct both endpoint factors on a common core.
This does not assume a relation arrow, an endpoint equation or a quotient theorem.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance fieldPairOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance fieldPairOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance fieldPairOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (J : A.IdealSheafData) {K : Type} [Field K]

/-- Two endpoints of the same exact rank acquire actual factors at every common order. -/
theorem exists_rankStage_field_boundary_pair (n : ℕ)
    (x y : Spec (.of K) ⟶ J.subscheme)
    (hx : (x ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n)
    (hy : (y ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n) :
    ∃ (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n),
      ∀ k, ∃ u v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme,
        u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = x ∧
        v ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = y := by
  let t : Bool → (Spec (.of K) ⟶ J.subscheme) := fun b ↦ if b then y else x
  have ht (b : Bool) : (t b ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈
      exactRank (Over.mk p) n := by
    cases b
    · exact hx
    · exact hy
  obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_family e J n t ht
  refine ⟨a, ha, fun k ↦ ?_⟩
  obtain ⟨u, hu, _⟩ := hc k false
  obtain ⟨v, hv, _⟩ := hc k true
  exact ⟨u, v, hu, hv⟩

/-- A field test factoring through a rank-core boundary has that exact original rank. -/
theorem rankStage_field_boundary_factor_exactRank (n : ℕ) (a : Γ(A, ⊤))
    (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
    (t : Spec (.of K) ⟶ J.subscheme)
    (u : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme)
    (hu : u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = t) :
    (t ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n := by
  rw [← hu, Category.assoc, rankStageCoreOriginalBoundaryMap,
    IdealSheafClosedTransitions.map_inclusion]
  apply (rankThickeningMap_range (Over.mk p) n k).le
  exact ⟨_, rfl⟩

/-- A common core is possible exactly when the two original field points have the same rank. -/
theorem rankStage_field_boundary_pair_iff_same_rank (x y : Spec (.of K) ⟶ J.subscheme) :
    (∃ (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
      (k : ℕ) (u v : Spec (.of K) ⟶ (rankStageCoreBoundaryIdeal e n a ha J k).subscheme),
      u ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = x ∧
      v ≫ rankStageCoreOriginalBoundaryMap e n a ha J k = y) ↔
    ∃ n, (x ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n ∧
      (y ≫ J.subschemeι) (IsLocalRing.closedPoint K) ∈ exactRank (Over.mk p) n := by
  constructor
  · rintro ⟨n, a, ha, k, u, v, hu, hv⟩
    exact ⟨n, rankStage_field_boundary_factor_exactRank e J n a ha k x u hu,
      rankStage_field_boundary_factor_exactRank e J n a ha k y v hv⟩
  · rintro ⟨n, hx, hy⟩
    obtain ⟨a, ha, hc⟩ := exists_rankStage_field_boundary_pair e J n x y hx hy
    obtain ⟨u, v, hu, hv⟩ := hc 0
    exact ⟨n, a, ha, 0, u, v, hu, hv⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
