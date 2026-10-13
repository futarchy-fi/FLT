/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueBranches
public import FLT.Mazur.WeierstrassCoefficientShearResidueInitialRightCharts
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentRightCharts
public import FLT.Mazur.WeierstrassCoefficientShearResidueEqualityEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Every complete residue branch retains its full horizontal chart

The signed reciprocal scale is kept at each original branch level. Equality on
the projective components therefore detects every entire retained line.
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

local notation "L" => coefficientShearResidueRetainedPair
  hπ hm data s hs hk hstart h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc

/-- Every complete branch has its entire original right chart, with its signed scale. -/
@[reassoc] theorem coefficientShearResidueBranchComponent_right
    (j : Fin (s + 1)) (i : Fin 2) :
    ProjectiveLine.right Q ≫ B j i =
      ProjectiveLine.chartScaling Q (if i = 0 then (a)⁻¹ else (-a)⁻¹) ≫ L j i := by
  by_cases hj : j.val = 0
  · have h : j = 0 := Fin.ext hj
    subst j
    rw [coefficientShearResidueBranchComponent_initial]
    fin_cases i
    · exact coefficientShearResidueInitialComponent_first_right ..
    · exact coefficientShearResidueInitialComponent_second_right ..
  · let k : Fin s := ⟨j.val - 1, by omega⟩
    have h : j = k.succ := Fin.ext (by dsimp [k]; omega)
    rw [h]
    change ProjectiveLine.right Q ≫ B ⟨k.val + 1, by omega⟩ i = _
    rw [coefficientShearResidueBranchComponent_adjacent
      hπ hm data s hs hk hstart h3 h4 h6 hc k i]
    fin_cases i
    · exact coefficientShearResidueAdjacentComponent_first_right ..
    · exact coefficientShearResidueAdjacentComponent_second_right ..

/-- Equality on a full branch component determines its entire retained horizontal line. -/
theorem coefficientShearResidueRetainedPair_hom_ext
    {Y : Scheme} (u v : coefficientShearGlued hπ data Q r (s + 1) hs ⟶ Y)
    (j : Fin (s + 1)) (i : Fin 2) (h : B j i ≫ u = B j i ≫ v) :
    L j i ≫ u = L j i ≫ v := by
  have H := congrArg (fun k => ProjectiveLine.right Q ≫ k) h
  rw [coefficientShearResidueBranchComponent_right_assoc,
    coefficientShearResidueBranchComponent_right_assoc] at H
  exact WeierstrassSuccessiveX.middleNode_cancel_chartScaling _ _ _ H

end FLT.Mazur.WeierstrassDividedDepth
