/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes

import all FLT.Mazur.WeierstrassCoefficientShearRetainedStage
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Full right charts of both original scale cases

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

/-- The first full right chart retains the next original line with its reciprocal scale. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_full_first_right :
    ProjectiveLine.right Q ≫ C 0 =
      ProjectiveLine.chartScaling Q (a)⁻¹ ≫ L 0 (middle_first_root U) := by
  unfold coefficientShearResidueAdjacentComponent
  simp only [ite_true]
  split_ifs with h
  · rw [← Category.assoc, coefficientShearAdjacentFirstComponent_right, Category.assoc]
    apply congrArg (ProjectiveLine.chartScaling Q (a)⁻¹ ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl
  · rw [← Category.assoc, coefficientShearScaleOneFirstComponent_right, Category.assoc]
    apply congrArg (ProjectiveLine.chartScaling Q (a)⁻¹ ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl

/-- The opposite full right chart retains the next line with the negative reciprocal scale. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_full_second_right :
    ProjectiveLine.right Q ≫ C 1 =
      ProjectiveLine.chartScaling Q (-a)⁻¹ ≫ L (-(U).a₁) (middle_second_root U) := by
  unfold coefficientShearResidueAdjacentComponent
  simp only [show (1 : Fin 2) ≠ 0 from by decide, ↓reduceIte]
  split_ifs with h
  · rw [← Category.assoc, coefficientShearAdjacentSecondComponent_right, Category.assoc]
    apply congrArg (ProjectiveLine.chartScaling Q (-a)⁻¹ ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl
  · rw [← Category.assoc, coefficientShearScaleOneSecondComponent_right, Category.assoc]
    apply congrArg (ProjectiveLine.chartScaling Q (-a)⁻¹ ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl

end FLT.Mazur.WeierstrassDividedDepth
