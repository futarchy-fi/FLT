/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints
public import FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes

import all FLT.Mazur.WeierstrassCoefficientShearRetainedStage
import all FLT.Mazur.WeierstrassCoefficientShearResidueRetainedNodes
import all FLT.Mazur.WeierstrassCoefficientShearResidueAdjacent
import all FLT.Mazur.WeierstrassCoefficientShearAdjacentEndpoints

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Both actual adjacent residue attachments at the common final stage

Each complete adjacent pair joins precisely the preceding and following retained
node pairs. Reindexing preserves the full original affine line parameters.
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

variable (hstart : 0 < start)
local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j
local notation "N" => coefficientShearResidueRetainedNode
  hπ hm data s hs hk hstart h3 h4

/-- Each adjacent zero is the preceding actual retained node, with its original branch index. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_zero (i : Fin 2) :
    ProjectiveLine.zero Q ≫ C i = N j.castSucc i := by
  unfold coefficientShearResidueAdjacentComponent coefficientShearResidueRetainedNode
    coefficientShearResidueRetainedLine
  rw [dite_eq_left (show 0 < start + j.val from by omega)]
  fin_cases i
  · simp only [Fin.ext_iff, Fin.val_zero, ↓reduceIte]
    rw [← Category.assoc, coefficientShearAdjacentFirstComponent_zero, Category.assoc]
    apply congrArg (ProjectiveLine.chartZero Q ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl
  · simp only [Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, ↓reduceIte]
    rw [← Category.assoc, coefficientShearAdjacentSecondComponent_zero, Category.assoc]
    apply congrArg (ProjectiveLine.chartZero Q ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl

/-- Each adjacent infinity is the next actual retained node, with no change of level. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinity Q ≫ C i = N j.succ i := by
  unfold coefficientShearResidueAdjacentComponent coefficientShearResidueRetainedNode
    coefficientShearResidueRetainedLine
  rw [dite_eq_left (show 0 < start + j.val from by omega)]
  fin_cases i
  · simp only [Fin.ext_iff, Fin.val_zero, ↓reduceIte]
    rw [← Category.assoc, coefficientShearAdjacentFirstComponent_infinity, Category.assoc]
    apply congrArg (ProjectiveLine.chartZero Q ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl
  · simp only [Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, ↓reduceIte]
    rw [← Category.assoc, coefficientShearAdjacentSecondComponent_infinity, Category.assoc]
    apply congrArg (ProjectiveLine.chartZero Q ≫ ·)
    apply coefficientShearRetainedLine_stageIso hπ data Q r
    rfl

end FLT.Mazur.WeierstrassDividedDepth
