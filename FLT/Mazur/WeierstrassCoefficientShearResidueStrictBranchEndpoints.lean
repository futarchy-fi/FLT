/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictAttachments
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranches
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictBranches

/-!
# Endpoints along the complete strict-depth branches

The assembled original chains retain every internal attachment, including the
last adjacent-to-terminal attachment and the common final terminal node.
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
local notation "C" => coefficientShearResidueStrictAdjacentBranch
  hπ hm data s hs hk h3 h4 h6 hc

/-- All consecutive extended adjacent components share the original retained node. -/
theorem coefficientShearResidueStrictAdjacentBranch_endpoints (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ C j.castSucc i = ProjectiveLine.zero Q ≫ C j.succ i := by
  unfold coefficientShearResidueStrictAdjacentBranch
  simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left j.isLt]
  split_ifs with hj
  · exact coefficientShearResidueStrictAdjacent_join
      hπ hm data s hs hk h3 h4 hc j hj i
  · have hjv : j.val = s - 1 := by omega
    simpa only [hjv] using coefficientShearResidueStrictAdjacent_terminal
      hπ hm data s hs hk h3 h4 h6 hc (by omega) i

/-- The full extended adjacent branches end at the same actual divided node. -/
theorem coefficientShearResidueStrictAdjacentBranch_final :
    ProjectiveLine.infinity Q ≫ C (Fin.last s) 0 =
      ProjectiveLine.infinity Q ≫ C (Fin.last s) 1 := by
  rw [coefficientShearResidueStrictAdjacentBranch_terminal,
    coefficientShearResidueStrictAdjacentBranch_terminal]
  exact coefficientShearResidueTerminalComponent_join hπ hm data s hs hk h3 h4 h6 hc

variable (hstart : 0 < start)
local notation "B" => coefficientShearResidueStrictPositiveBranch
  hπ hm data s hs hk h3 h4 h6 hc hstart

/-- All complete positive-start branch positions retain their matching internal endpoints. -/
theorem coefficientShearResidueStrictPositiveBranch_endpoints (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ B j.castSucc i = ProjectiveLine.zero Q ≫ B j.succ i := by
  unfold coefficientShearResidueStrictPositiveBranch
  simp only [Fin.val_castSucc, Fin.val_succ, dite_eq_left j.isLt]
  split_ifs with hj
  · exact coefficientShearResidueBranchComponent_endpoints
      hπ hm data s hs (Nat.le_of_lt hk) hstart h3 h4 h6 hc ⟨j.val, by omega⟩ i
  · have hjv : j = Fin.last s := Fin.ext (by dsimp; omega)
    subst j
    exact coefficientShearResidueStrictBranch_terminal hπ hm data s hs hk h3 h4 h6 hc hstart i

/-- The complete positive-start branches share the actual final terminal node. -/
theorem coefficientShearResidueStrictPositiveBranch_final :
    ProjectiveLine.infinity Q ≫ B (Fin.last (s + 1)) 0 =
      ProjectiveLine.infinity Q ≫ B (Fin.last (s + 1)) 1 := by
  rw [coefficientShearResidueStrictPositiveBranch_terminal,
    coefficientShearResidueStrictPositiveBranch_terminal]
  exact coefficientShearResidueTerminalComponent_join hπ hm data s hs hk h3 h4 h6 hc

end FLT.Mazur.WeierstrassDividedDepth
