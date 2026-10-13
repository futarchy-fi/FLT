/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueEqualityEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Actual node identifications along both full residue branches

Every branch infinity is the retained node at the same level. A subsequent
component starts at the preceding node, so the complete branches glue there.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "N" => coefficientShearResidueRetainedNode
  hπ hm data s hs hk hstart h3 h4

/-- Every full branch component ends at the actual retained node at its own level. -/
@[reassoc] theorem coefficientShearResidueBranchComponent_infinity
    (j : Fin (s + 1)) (i : Fin 2) : ProjectiveLine.infinity Q ≫ B j i = N j i := by
  by_cases hj : j.val = 0
  · have h : j = 0 := Fin.ext hj
    subst j
    rw [coefficientShearResidueBranchComponent_initial,
      coefficientShearResidueInitialComponent_infinity]
  · let k : Fin s := ⟨j.val - 1, by omega⟩
    have h : j = k.succ := Fin.ext (by dsimp [k]; omega)
    rw [h]
    change ProjectiveLine.infinity Q ≫ B ⟨k.val + 1, by omega⟩ i = N k.succ i
    rw [coefficientShearResidueBranchComponent_adjacent
      hπ hm data s hs hk hstart h3 h4 h6 hc k i]
    exact coefficientShearResidueAdjacentComponent_infinity
      hπ hm data s hs hk h3 h4 hc k hstart i

/-- Each subsequent component begins at the preceding actual retained node. -/
@[reassoc] theorem coefficientShearResidueBranchComponent_succ_zero
    (j : Fin s) (i : Fin 2) : ProjectiveLine.zero Q ≫ B j.succ i = N j.castSucc i := by
  change ProjectiveLine.zero Q ≫ B ⟨j.val + 1, by omega⟩ i = N j.castSucc i
  rw [coefficientShearResidueBranchComponent_adjacent
    hπ hm data s hs hk hstart h3 h4 h6 hc j i]
  exact coefficientShearResidueAdjacentComponent_zero
    hπ hm data s hs hk h3 h4 hc j hstart i

/-- Both independently completed branches have actual matching internal endpoints. -/
theorem coefficientShearResidueBranchComponent_endpoints (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ B j.castSucc i = ProjectiveLine.zero Q ≫ B j.succ i := by
  rw [coefficientShearResidueBranchComponent_infinity,
    coefficientShearResidueBranchComponent_succ_zero]

variable (he : 2 * (start + (s + 1)) = depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1))
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc

/-- The first complete branch ends at zero of the independently completed equality terminal. -/
theorem coefficientShearResidueBranchComponent_terminal_first :
    ProjectiveLine.infinity Q ≫ B ⟨s, by omega⟩ 0 = ProjectiveLine.zero Q ≫ T := by
  rw [coefficientShearResidueBranchComponent_infinity,
    coefficientShearResidueEqualityComponent_zero hπ hm data s hs he h3 h4 h6next hc hstart]

/-- The opposite complete branch ends at infinity of that same actual terminal component. -/
theorem coefficientShearResidueBranchComponent_terminal_second :
    ProjectiveLine.infinity Q ≫ B ⟨s, by omega⟩ 1 = ProjectiveLine.infinity Q ≫ T := by
  rw [coefficientShearResidueBranchComponent_infinity,
    coefficientShearResidueEqualityComponent_infinity
      hπ hm data s hs he h3 h4 h6next hc hstart]

end FLT.Mazur.WeierstrassDividedDepth
