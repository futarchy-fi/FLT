/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminal

/-!
# Complete original branches at strict depth

The independent terminal pair extends the complete adjacent chains. Positive
starts retain the initial pair; zero starts begin with the actual first adjacent
pair. Both assemblies retain every full projective parameter under conjugation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "A" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc

/-- The full adjacent chain followed by the original independent terminal pair. -/
def coefficientShearResidueStrictAdjacentBranch (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if h : j.val < s then A ⟨j.val, h⟩ i else T i
local notation "C" => coefficientShearResidueStrictAdjacentBranch
  hπ hm data s hs hk h3 h4 h6 hc

/-- Every original adjacent component retains its entire parameter. -/
theorem coefficientShearResidueStrictAdjacentBranch_adjacent (j : Fin s) (i : Fin 2) :
    C j.castSucc i = A j i := by
  simp only [coefficientShearResidueStrictAdjacentBranch, Fin.val_castSucc,
    dite_eq_left j.isLt]

/-- The final position is precisely the original strict terminal pair. -/
theorem coefficientShearResidueStrictAdjacentBranch_terminal (i : Fin 2) :
    C (Fin.last s) i = T i := by
  simp only [coefficientShearResidueStrictAdjacentBranch, Fin.val_last, lt_self_iff_false,
    dite_false]

/-- The full extended adjacent chain is over the original residue field. -/
@[reassoc] theorem coefficientShearResidueStrictAdjacentBranch_structure
    (j : Fin (s + 1)) (i : Fin 2) : C j i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueStrictAdjacentBranch
  split_ifs
  · exact coefficientShearResidueAdjacentComponent_structure ..
  · exact coefficientShearResidueTerminalComponent_structure ..

/-- Conjugation exchanges both complete extended adjacent chains at every level. -/
@[reassoc] theorem coefficientShearResidueStrictAdjacentBranch_conjugation
    (j : Fin (s + 1)) (i : Fin 2) : C j i ≫ σ = P ≫ C j i.rev := by
  unfold coefficientShearResidueStrictAdjacentBranch
  split_ifs
  · exact coefficientShearResidueAdjacentComponent_conjugation ..
  · exact coefficientShearResidueTerminalComponent_conjugation ..

variable (hstart : 0 < start)
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc

/-- Positive starts retain the initial pair and append the entire terminal pair. -/
def coefficientShearResidueStrictPositiveBranch (j : Fin (s + 2)) (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if h : j.val < s + 1 then B ⟨j.val, h⟩ i else T i
local notation "D" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart

/-- All original nonterminal positions retain their full branch maps. -/
theorem coefficientShearResidueStrictPositiveBranch_branch (j : Fin (s + 1)) (i : Fin 2) :
    D j.castSucc i = B j i := by
  simp only [coefficientShearResidueStrictPositiveBranch, Fin.val_castSucc,
    dite_eq_left j.isLt]

/-- The final positive-start position is the full independent terminal pair. -/
theorem coefficientShearResidueStrictPositiveBranch_terminal (i : Fin 2) :
    D (Fin.last (s + 1)) i = T i := by
  simp only [coefficientShearResidueStrictPositiveBranch, Fin.val_last, lt_self_iff_false,
    dite_false]

/-- Each complete positive-start branch preserves the original coefficient structure. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveBranch_structure
    (j : Fin (s + 2)) (i : Fin 2) : D j i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueStrictPositiveBranch
  split_ifs
  · exact coefficientShearResidueBranchComponent_structure ..
  · exact coefficientShearResidueTerminalComponent_structure ..

/-- Full semilinear exchange retains each original positive-start branch parameter. -/
@[reassoc] theorem coefficientShearResidueStrictPositiveBranch_conjugation
    (j : Fin (s + 2)) (i : Fin 2) : D j i ≫ σ = P ≫ D j i.rev := by
  unfold coefficientShearResidueStrictPositiveBranch
  split_ifs
  · exact coefficientShearResidueBranchComponent_conjugation ..
  · exact coefficientShearResidueTerminalComponent_conjugation ..

end FLT.Mazur.WeierstrassDividedDepth
