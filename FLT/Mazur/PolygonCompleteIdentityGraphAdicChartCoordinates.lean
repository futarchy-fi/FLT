/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicNode

/-!
# Original node maps and coefficients on the actual graph charts

The affine charts map into the previously constructed full original node
correspondences. Both node coordinates have exactly the graph's original
truncated coefficient map. The source still carries its full Laurent unit.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "x" => completeIdentityActionGraphAdicChartSource K n h m i j
local notation "y" => completeIdentityActionGraphAdicChartTarget K n h m i j
local notation "v" => completeIdentityActionGraphAdicChartInclusion K n h m i j
local notation "b" => Spec.map (CommRingCat.ofHom (LaurentPolynomial.C : (A) →+* (A)[T;T⁻¹]))
local notation "s" => completeIdentityActionGraphAdicChartStructure K n h m i j

/-- Each affine graph chart maps into the entire original source-node correspondence. -/
def completeIdentityActionGraphAdicChartToNode :
    completeIdentityActionGraphAdicChart K n h m i j ⟶
      completeIdentityActionGraphAdicNode K n h m i :=
  pullback.lift (v) (x) (completeIdentityActionGraphAdicChartSource_inclusion K n h m i j).symm

@[reassoc] theorem completeIdentityActionGraphAdicChartToNode_inclusion :
    completeIdentityActionGraphAdicChartToNode K n h m i j ≫
        completeIdentityActionGraphAdicNodeInclusion K n h m i = (v) :=
  pullback.lift_fst _ _ _

@[reassoc] theorem completeIdentityActionGraphAdicChartToNode_source :
    completeIdentityActionGraphAdicChartToNode K n h m i j ≫
        completeIdentityActionGraphAdicNodeProjection K n h m i = (x) :=
  pullback.lift_snd _ _ _

/-- The original source-node lift restricts to the actual target node coordinate. -/
@[reassoc] theorem completeIdentityActionGraphAdicChartToNode_target :
    completeIdentityActionGraphAdicChartToNode K n h m i j ≫
        completeIdentityActionGraphAdicNodeLift K n h m i =
      (y) ≫ PolygonInfinitesimal.chart (A) (t) n h j := by
  rw [completeIdentityActionGraphAdicNodeLift,
    completeIdentityActionGraphAdicChartToNode_inclusion_assoc,
    completeIdentityActionGraphAdicChartTarget_inclusion]

/-- The target node coordinate uses the literal original truncated coefficient map. -/
@[reassoc] theorem completeIdentityActionGraphAdicChartTarget_structure :
    (y) ≫ chartStructure (A) (t) = (s) := by
  rw [← chart_toBase (A) (t) n h j, ← Category.assoc,
    completeIdentityActionGraphAdicChartTarget_inclusion, Category.assoc]
  change (v) ≫ completeIdentityActionGraphStageOriginalLift K n h m ≫
    (family K m n h).hom = (s)
  rw [completeIdentityActionGraphStageOriginalLift_structure]
  rfl

/-- The source node retains its full Laurent parameter over the same original truncated base. -/
@[reassoc] theorem completeIdentityActionGraphAdicChartSource_structure :
    (x) ≫ chartStructure (A)[T;T⁻¹] (LaurentPolynomial.C (t)) ≫ (b) = (s) := by
  unfold completeIdentityActionGraphAdicChartStructure
  rw [← completeIdentityActionGraphStageOriginalProjection_structure,
    ← completeIdentityActionGraphAdicChartSource_inclusion_assoc]
  change _ = (x) ≫ PolygonInfinitesimal.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i ≫
    parameterProjection LaurentPolynomial.C (t) (LaurentPolynomial.C (t)) rfl n h ≫
      toBase (A) (t) n h
  rw [parameterProjection_base, chart_toBase_assoc]

end FLT.Mazur.PolygonInfinitesimalStages
