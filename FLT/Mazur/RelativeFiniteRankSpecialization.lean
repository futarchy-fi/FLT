/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameRankPullback
public import FLT.Mazur.RelativeFiniteFrameRankClosed

/-!
# Finite original pullbacks cannot lose rank along specialization

Finiteness closes every frame image of the entire pulled-back source.
Thus rank is preserved along every specialization in the coefficient scheme,
even when that scheme is nonflat over the original geometric base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]

/-- Exact rank pieces of the full finite original source are closed. -/
theorem exactRank_isClosed_of_finite [IsFinite E.hom] (n : ℕ) :
    IsClosed (exactRank E n) :=
  (rankImageOpen_isClosed_of_finite E n).inter (rankAtMost_isClosed E n)

/-- A finite original source preserves exact rank in both directions of specialization. -/
theorem exactRank_specializes_iff_of_finite [IsFinite E.hom]
    {x y : S} (hxy : x ⤳ y) (n : ℕ) :
    x ∈ exactRank E n ↔ y ∈ exactRank E n := by
  constructor
  · intro hx
    exact closure_minimal (Set.singleton_subset_iff.mpr hx)
      (exactRank_isClosed_of_finite E n) hxy.mem_closure
  · intro hy
    refine ⟨hxy.mem_open (rankImageOpen E n).isOpen hy.1, ?_⟩
    intro hx
    have hy' := closure_minimal (Set.singleton_subset_iff.mpr hx)
      (rankImageOpen_isClosed_of_finite E (n + 1)) hxy.mem_closure
    exact hy.2 hy'

variable [QuasiCompact E.hom] (b : B ⟶ S)
local instance finiteRankPullback_etale : Etale (Over.mk (pullback.snd E.hom b)).hom :=
  inferInstanceAs (Etale (pullback.snd E.hom b))
local instance finiteRankPullback_separated : IsSeparated (Over.mk (pullback.snd E.hom b)).hom :=
  inferInstanceAs (IsSeparated (pullback.snd E.hom b))

/-- Finiteness of the full coefficient pullback prevents loss of original rank. -/
theorem exactRank_specializes_iff_of_finite_pullback [IsFinite (pullback.snd E.hom b)]
    {x y : B} (hxy : x ⤳ y) (n : ℕ) :
    b x ∈ exactRank E n ↔ b y ∈ exactRank E n := by
  let _ : IsFinite (Over.mk (pullback.snd E.hom b)).hom :=
    inferInstanceAs (IsFinite (pullback.snd E.hom b))
  rw [← exactRank_pullback_iff E b x, ← exactRank_pullback_iff E b y]
  exact exactRank_specializes_iff_of_finite (Over.mk (pullback.snd E.hom b)) hxy n

/-- Strict rank loss proves that the full original coefficient pullback is not finite. -/
theorem not_finite_pullback_of_rank_drop {x y : B} (hxy : x ⤳ y) {n m : ℕ}
    (hx : b x ∈ exactRank E n) (hy : b y ∈ exactRank E m) (hnm : n ≠ m) :
    ¬ IsFinite (pullback.snd E.hom b) := by
  intro hf
  let _ := hf
  have hn := (exactRank_specializes_iff_of_finite_pullback E b hxy n).mp hx
  exact Set.disjoint_left.mp (exactRank_disjoint E hnm) hn hy

end FLT.Mazur.RelativeOrderedTuples
