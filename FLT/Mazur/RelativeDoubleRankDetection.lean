/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankThickenings
public import FLT.Mazur.RelativeRankStageSectionDetection

/-!
# Full section detection by independent endpoint rank stages

Iterated rank stages detect whole sections on locally Noetherian coefficients.
Both infinitesimal orders are retained, so this is stronger than field-point
coverage. No flat descent claim or equality of the two ranks is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} [IsNoetherian S]
  (E : Over S) [Etale E.hom] [IsSeparated E.hom] (x y : B ⟶ S)

instance rankPullbackThickening_isLocallyNoetherian [IsLocallyNoetherian B] (n r : ℕ) :
    IsLocallyNoetherian (rankPullbackThickening E x n r) := by
  unfold rankPullbackThickening
  infer_instance

variable [IsLocallyNoetherian B]

/-- Any independently covering rank sets detect the full coefficient section. -/
theorem section_zero_of_doubleRank_stages (leftRanks rightRanks : Set ℕ)
    (hx : ∀ z : B, ∃ n ∈ leftRanks, x z ∈ exactRank E n)
    (hy : ∀ z : B, ∃ m ∈ rightRanks, y z ∈ exactRank E m) (a : Γ(B, ⊤))
    (ha : ∀ n ∈ leftRanks, ∀ m ∈ rightRanks, ∀ r s : ℕ,
      (doubleRankMap E x y n m r s).appTop a = 0) : a = 0 := by
  apply section_zero_of_rank_stages E x leftRanks hx a
  intro n hn r
  apply section_zero_of_rank_stages E (rankPullbackMap E x n r ≫ y)
    rightRanks (fun z ↦ hy (rankPullbackMap E x n r z))
  intro m hm s
  change ((rankPullbackMap E x n r).appTop ≫
    (rankPullbackMap E (rankPullbackMap E x n r ≫ y) m s).appTop) a = 0
  rw [← Scheme.Hom.comp_appTop]
  exact ha n hn m hm r s

/-- The iterated thickening detects actual equality, including nilpotent coefficients. -/
theorem section_eq_of_doubleRank_stages (leftRanks rightRanks : Set ℕ)
    (hx : ∀ z : B, ∃ n ∈ leftRanks, x z ∈ exactRank E n)
    (hy : ∀ z : B, ∃ m ∈ rightRanks, y z ∈ exactRank E m) (a b : Γ(B, ⊤))
    (hab : ∀ n ∈ leftRanks, ∀ m ∈ rightRanks, ∀ r s : ℕ,
      (doubleRankMap E x y n m r s).appTop a =
        (doubleRankMap E x y n m r s).appTop b) : a = b := by
  apply sub_eq_zero.mp
  apply section_zero_of_doubleRank_stages E x y leftRanks rightRanks hx hy (a - b)
  intro n hn m hm r s
  rw [map_sub, hab n hn m hm r s, sub_self]

variable [QuasiCompact E.hom]

/-- All independent ranks and orders jointly detect full original sections. -/
theorem section_eq_iff_doubleRank_stages (a b : Γ(B, ⊤)) :
    a = b ↔ ∀ n m r s : ℕ,
      (doubleRankMap E x y n m r s).appTop a =
        (doubleRankMap E x y n m r s).appTop b := by
  refine ⟨fun h _ _ _ _ ↦ congrArg _ h, fun h ↦ ?_⟩
  refine section_eq_of_doubleRank_stages E x y Set.univ Set.univ ?_ ?_ a b ?_
  · intro z
    obtain ⟨n, hn⟩ := exists_exactRank E (x z)
    exact ⟨n, Set.mem_univ n, hn⟩
  · intro z
    obtain ⟨m, hm⟩ := exists_exactRank E (y z)
    exact ⟨m, Set.mem_univ m, hm⟩
  · exact fun n _ m _ ↦ h n m

end FLT.Mazur.RelativeOrderedTuples
