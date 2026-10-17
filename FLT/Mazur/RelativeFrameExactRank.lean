/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFrameUniformRank
public import Mathlib.Topology.LocallyClosed

/-!
# Exact rank strata, including the residual closed locus

The complements of larger-frame images form an increasing closed filtration.
Its locally closed differences cover every original point, unlike the open
rank strata. These sets impose no reduction on any scheme supported on them.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]

/-- Having more distinct original arrows implies having every smaller frame. -/
theorem rankImageOpen_antitone : Antitone (rankImageOpen E) := by
  intro n m hnm x hx
  obtain ⟨y, hy⟩ := hx
  refine ⟨(subframe E (Fin.castLEEmb hnm)).left y, ?_⟩
  exact (congrArg (fun f ↦ f y) (subframe E (Fin.castLEEmb hnm)).w).trans hy

/-- The closed locus on which no larger original frame exists. -/
def rankAtMost (n : ℕ) : Set S := (rankImageOpen E (n + 1) : Set S)ᶜ

/-- Exact rank retains lower-rank points on the boundary of larger-frame images. -/
def exactRank (n : ℕ) : Set S := (rankImageOpen E n : Set S) ∩ rankAtMost E n

/-- Rank bounds cut out closed subsets of the unchanged base. -/
theorem rankAtMost_isClosed (n : ℕ) : IsClosed (rankAtMost E n) :=
  (rankImageOpen E (n + 1)).isOpen.isClosed_compl

/-- Increasing the bound enlarges the actual closed rank locus. -/
theorem rankAtMost_mono : Monotone (rankAtMost E) := by
  intro n m hnm x hx hm
  exact hx (rankImageOpen_antitone E (Nat.succ_le_succ hnm) hm)

/-- Each exact rank piece is locally closed in the original base. -/
theorem exactRank_isLocallyClosed (n : ℕ) : IsLocallyClosed (exactRank E n) :=
  (rankImageOpen E n).isOpen.isLocallyClosed.inter (rankAtMost_isClosed E n).isLocallyClosed

/-- Different exact ranks are disjoint, including on the residual locus. -/
theorem exactRank_disjoint {n m : ℕ} (hnm : n ≠ m) :
    Disjoint (exactRank E n) (exactRank E m) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hnm with h | h
  · exact hx.2 (rankImageOpen_antitone E h hy.1)
  · exact hy.2 (rankImageOpen_antitone E h hx.1)

variable [QuasiCompact E.hom]

/-- Every original point belongs to an exact rank stratum, not merely a dense open. -/
theorem exists_exactRank (x : S) : ∃ n : ℕ, x ∈ exactRank E n := by
  obtain ⟨n, hn⟩ := exists_point_rank E x
  exact ⟨n, (hn n).mpr le_rfl, fun h ↦ Nat.not_succ_le_self n ((hn (n + 1)).mp h)⟩

/-- The exact rank pieces cover the whole original space. -/
theorem iUnion_exactRank : (⋃ n : ℕ, exactRank E n) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact Set.mem_iUnion.mpr (exists_exactRank E x)

/-- On a noetherian base, finitely many of these locally closed pieces suffice. -/
theorem exists_finite_exactRank_cover [NoetherianSpace S] :
    ∃ N : ℕ, ∀ x : S, ∃ n ≤ N, x ∈ exactRank E n := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound E
  refine ⟨N, fun x ↦ ?_⟩
  obtain ⟨n, hn⟩ := exists_exactRank E x
  exact ⟨n, hN x n hn.1, hn⟩

end FLT.Mazur.RelativeOrderedTuples
