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
# The actual retained residue node sections

Construct the ordered node sections from the retained line origins at the common
final stage. Nodal depth bounds supply all coefficient and root hypotheses.
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
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))

local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
variable (j : Fin (s + 1))
local notation "d" => data ⟨j.val + 1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + j.val from by omega)
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "line" => coefficientShearRetainedLine hπ data Q r (s + 1) hs j
  hscale hp (lin).1 (lin).2 (residueTangentEquation_root W)

/-- The complete retained pair at the original common stage, with its ordered tangent roots. -/
def coefficientShearResidueRetainedLine (i : Fin 2) :
    ProjectiveLine.chart Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if i = 0 then line 0 (middle_first_root U)
  else line (-(U).a₁) (middle_second_root U)
local notation "L" => coefficientShearResidueRetainedLine
  hπ hm data s hs hk hstart h3 h4 j

/-- The node is the actual retained affine origin, not a separately specified point. -/
def coefficientShearResidueRetainedNode (i : Fin 2) :
    Spec (.of Q) ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  ProjectiveLine.chartZero Q ≫ L i
local notation "N" => coefficientShearResidueRetainedNode
  hπ hm data s hs hk hstart h3 h4 j

/-- Each complete retained line has the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueRetainedLine_structure (i : Fin 2) :
    L i ≫ coefficientShearGluedStructure hπ data Q r (s + 1) hs =
      ProjectiveLine.chartToBase Q := by
  unfold coefficientShearResidueRetainedLine
  split_ifs <;> exact coefficientShearRetainedLine_structure ..

/-- Each actual retained node is a section over the original residue tangent field. -/
@[reassoc] theorem coefficientShearResidueRetainedNode_structure (i : Fin 2) :
    N i ≫ coefficientShearGluedStructure hπ data Q r (s + 1) hs = 𝟙 _ := by
  rw [coefficientShearResidueRetainedNode, Category.assoc,
    coefficientShearResidueRetainedLine_structure, ProjectiveLine.chartZero_toBase]

end FLT.Mazur.WeierstrassDividedDepth
