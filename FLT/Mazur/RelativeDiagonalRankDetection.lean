/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankClosedLifts
public import FLT.Mazur.RelativeRankCollisionIdeal

/-!
# Diagonal detection with the full off-diagonal obstruction retained

A common-rank condition makes every off-diagonal thickening genuinely empty.
Only under that condition do the diagonal two-order stages detect sections
and construct arrows through a closed comparison. Both orders remain free.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Z Y : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S)

/-- A common-rank test has no off-diagonal coefficient scheme at any pair of orders. -/
theorem doubleRank_isEmpty_of_common_ranks
    (h : ∀ z : B, ∃ n, x z ∈ exactRank E n ∧ y z ∈ exactRank E n)
    (n m r s : ℕ) (hnm : n ≠ m) : IsEmpty (doubleRankThickening E x y n m r s) := by
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨k, hx, hy⟩ := h (doubleRankMap E x y n m r s z)
  obtain ⟨hn, hm⟩ := doubleRankMap_endpoints E x y n m r s z
  have hnk : n = k := by
    by_contra hne
    exact Set.disjoint_left.mp (exactRank_disjoint E hne) hn hx
  have hmk : m = k := by
    by_contra hne
    exact Set.disjoint_left.mp (exactRank_disjoint E hne) hm hy
  exact hnm (hnk.trans hmk.symm)

variable [QuasiCompact E.hom]

/-- Vanishing of the entire off-diagonal family is exactly the pointwise rank obstruction. -/
theorem common_ranks_iff_offDiagonal_empty (r s : ℕ) :
    (∀ z : B, ∃ n, x z ∈ exactRank E n ∧ y z ∈ exactRank E n) ↔
      ∀ n m : ℕ, n ≠ m → IsEmpty (doubleRankThickening E x y n m r s) := by
  refine ⟨fun h n m hnm ↦ doubleRank_isEmpty_of_common_ranks E x y h n m r s hnm, ?_⟩
  intro h z
  obtain ⟨n, m, w, hw⟩ := exists_doubleRank_lift E x y r s z
  have hnm : n = m := by
    by_contra hne
    exact (h n m hne).false w
  subst m
  refine ⟨n, ?_⟩
  simpa only [hw] using doubleRankMap_endpoints E x y n n r s w

variable [IsNoetherian S] [IsLocallyNoetherian B]

/-- All diagonal orders detect full coefficients once the off-diagonal schemes are empty. -/
theorem section_eq_of_diagonalRank_stages
    (h : ∀ z : B, ∃ n, x z ∈ exactRank E n ∧ y z ∈ exactRank E n)
    (a b : Γ(B, ⊤))
    (hab : ∀ n r s : ℕ, (doubleRankMap E x y n n r s).appTop a =
      (doubleRankMap E x y n n r s).appTop b) : a = b := by
  apply (section_eq_iff_doubleRank_stages E x y a b).mpr
  intro n m r s
  by_cases hnm : n = m
  · subst m
    exact hab n r s
  · let _ := doubleRank_isEmpty_of_common_ranks E x y h n m r s hnm
    exact Subsingleton.elim _ _

/-- No arrow is presumed on an off-diagonal stage: its empty scheme supplies the arrow. -/
theorem existsUnique_lift_of_diagonalRank [IsAffine B]
    (h : ∀ z : B, ∃ n, x z ∈ exactRank E n ∧ y z ∈ exactRank E n)
    (c : Z ⟶ Y) [Mono c] (t : B ⟶ Y) [IsClosedImmersion (pullback.snd c t)]
    (hl : ∀ n r s : ℕ, ∃ d : doubleRankThickening E x y n n r s ⟶ Z,
      d ≫ c = doubleRankMap E x y n n r s ≫ t) :
    ∃! d : B ⟶ Z, d ≫ c = t := by
  apply existsUnique_lift_of_doubleRank E x y c t
  intro n m r s
  by_cases hnm : n = m
  · subst m
    exact hl n r s
  · let _ := doubleRank_isEmpty_of_common_ranks E x y h n m r s hnm
    exact ⟨isInitialOfIsEmpty.to Z, isInitialOfIsEmpty.hom_ext _ _⟩

end FLT.Mazur.RelativeOrderedTuples
