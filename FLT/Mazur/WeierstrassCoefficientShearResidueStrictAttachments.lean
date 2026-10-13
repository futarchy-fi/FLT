/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueTerminalEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueBranchEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentPositiveEndpoints
import all FLT.Mazur.WeierstrassCoefficientShearResiduePositiveRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Original attachments to the full strict-depth terminal pair

The last adjacent pair attaches to the terminal pair at either start. Positive
starts also cover length zero, where the original initial pair is last.
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
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "A" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc

/-- Consecutive full adjacent components retain their common original node at strict depth. -/
theorem coefficientShearResidueStrictAdjacent_join (j : Fin s) (hj : j.val + 1 < s)
    (i : Fin 2) : ProjectiveLine.infinity Q ≫ A j i =
      ProjectiveLine.zero Q ≫ A ⟨j.val + 1, hj⟩ i := by
  rw [coefficientShearResidueAdjacentComponent_infinity_positive,
    coefficientShearResidueAdjacentComponent_zero_positive
      hπ hm data s hs (Nat.le_of_lt hk) h3 h4 hc ⟨j.val + 1, hj⟩ (by dsimp; omega)]
  rfl

/-- Each last adjacent component meets the matching full original strict terminal component. -/
theorem coefficientShearResidueStrictAdjacent_terminal (hspos : 0 < s) (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ A ⟨s - 1, by omega⟩ i = ProjectiveLine.zero Q ≫ T i := by
  rw [coefficientShearResidueAdjacentComponent_infinity_positive,
    coefficientShearResidueTerminalComponent_zero_positive
      hπ hm data s hs hk h3 h4 h6 hc (by omega)]
  have hi : (⟨s - 1, by omega⟩ : Fin s).succ = (⟨s, by omega⟩ : Fin (s + 1)) :=
    Fin.ext (by dsimp; omega)
  simp only [hi]

variable (hstart : 0 < start)
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc

/-- The original positive-start branches meet the entire strict terminal pair, even at s=0. -/
theorem coefficientShearResidueStrictBranch_terminal (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ B (Fin.last s) i = ProjectiveLine.zero Q ≫ T i := by
  rw [coefficientShearResidueBranchComponent_infinity,
    coefficientShearResidueTerminalComponent_zero_positive
      hπ hm data s hs hk h3 h4 h6 hc (by omega)]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
