/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearRetainedStage

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Retained residue node sections at each positive level

The retained origins require positivity only at their own level. In particular,
start zero is allowed at every later level, without inventing an initial pair.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX
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

local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (j : Fin (s + 1)) (hlevel : 0 < start + j.val)
local notation "d" => data ⟨j.val + 1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  hlevel
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "line" => coefficientShearRetainedLine hπ data Q r (s + 1) hs j
  hscale hp (lin).1 (lin).2 (residueTangentEquation_root W)

/-- The complete retained pair at the original common stage, with its ordered tangent roots. -/
def coefficientShearResiduePositiveRetainedPair (i : Fin 2) :
    ProjectiveLine.chart Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if i = 0 then line 0 (middle_first_root U)
  else line (-(U).a₁) (middle_second_root U)
local notation "L" => coefficientShearResiduePositiveRetainedPair
  hπ hm data s hs hk h3 h4 j hlevel

/-- The node is the actual retained affine origin, not a separately specified point. -/
def coefficientShearResiduePositiveRetainedNode (i : Fin 2) :
    Spec (.of Q) ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  ProjectiveLine.chartZero Q ≫ L i
local notation "N" => coefficientShearResiduePositiveRetainedNode
  hπ hm data s hs hk h3 h4 j hlevel

/-- Each complete retained line has the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResiduePositiveRetainedPair_structure (i : Fin 2) :
    L i ≫ coefficientShearGluedStructure hπ data Q r (s + 1) hs =
      ProjectiveLine.chartToBase Q := by
  unfold coefficientShearResiduePositiveRetainedPair
  split_ifs <;> exact coefficientShearRetainedLine_structure ..

/-- Each actual retained node is a section over the original residue tangent field. -/
@[reassoc] theorem coefficientShearResiduePositiveRetainedNode_structure (i : Fin 2) :
    N i ≫ coefficientShearGluedStructure hπ data Q r (s + 1) hs = 𝟙 _ := by
  rw [coefficientShearResiduePositiveRetainedNode, Category.assoc,
    coefficientShearResiduePositiveRetainedPair_structure, ProjectiveLine.chartZero_toBase]

end FLT.Mazur.WeierstrassDividedDepth
