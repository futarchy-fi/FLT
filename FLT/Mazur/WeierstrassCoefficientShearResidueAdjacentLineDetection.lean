/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentFullRight
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes

import all FLT.Mazur.WeierstrassCoefficientShearRetainedStage
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Complete adjacent components detect both next retained lines

The original retained lines at the next level survive the common-stage transport
with their complete parameters and signed reciprocal scaling.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open FLT.Mazur.WeierstrassModificationX FLT.Mazur.WeierstrassSuccessiveX
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (j : Fin s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "m" => s - (j.val + 1)
local notation "hs'" => show j.val + 2 + m ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "E" => coefficientShearStageIso hπ data Q r
  (j.val + 2 + m) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + j.succ.val from by simp only [Fin.val_succ]; omega)
local notation "L" => coefficientShearRetainedLine hπ data Q r (s + 1) hs j.succ
  hscale hp (lin).1 (lin).2 hr
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r

variable {Y : Scheme} (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)

/-- The entire first adjacent component determines the whole next first horizontal line. -/
theorem coefficientShearResidueAdjacentFirstLine_hom_ext (h : C 0 ≫ u = C 0 ≫ v) :
    L 0 (middle_first_root U) ≫ u = L 0 (middle_first_root U) ≫ v := by
  have H := congrArg (fun k => ProjectiveLine.right Q ≫ k) h
  rw [coefficientShearResidueAdjacentComponent_full_first_right_assoc,
    coefficientShearResidueAdjacentComponent_full_first_right_assoc] at H
  exact WeierstrassSuccessiveX.middleNode_cancel_chartScaling _ _ _ H

/-- The entire opposite component determines the whole next second horizontal line. -/
theorem coefficientShearResidueAdjacentSecondLine_hom_ext (h : C 1 ≫ u = C 1 ≫ v) :
    L (-(U).a₁) (middle_second_root U) ≫ u =
      L (-(U).a₁) (middle_second_root U) ≫ v := by
  have H := congrArg (fun k => ProjectiveLine.right Q ≫ k) h
  rw [coefficientShearResidueAdjacentComponent_full_second_right_assoc,
    coefficientShearResidueAdjacentComponent_full_second_right_assoc] at H
  exact WeierstrassSuccessiveX.middleNode_cancel_chartScaling _ _ _ H

end FLT.Mazur.WeierstrassDividedDepth
