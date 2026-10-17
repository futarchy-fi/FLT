/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# Lifting actual adic graph maps into the original node charts

A graph map whose two coordinates factor through specified original nodes
factors through the literal graph chart, preserving both full coordinates.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m
local notation "l" => completeIdentityActionGraphStageOriginalLift K n h m
local notation "s" => chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "d" => chart (A) (t) n h j
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m
local notation "v" => completeIdentityActionAdicChartSpaceMap K n h m i j
variable {T : Scheme} (f : T ⟶ completeIdentityActionGraphStage K n h m)
  (x : T ⟶ PolygonSmoothing.chart (Ring K m)[T;T⁻¹]
    (LaurentPolynomial.C (parameter K m)))
  (y : T ⟶ PolygonSmoothing.chart (Ring K m) (parameter K m))
  (hx : x ≫ chart (Ring K m)[T;T⁻¹] (LaurentPolynomial.C (parameter K m)) n h i =
    f ≫ completeIdentityActionGraphStageOriginalProjection K n h m)
  (hy : y ≫ chart (Ring K m) (parameter K m) n h j =
    f ≫ completeIdentityActionGraphStageOriginalLift K n h m)

/-- The factored coordinates satisfy the exact original node-pair cubic equation. -/
def completeIdentityGraphChartLiftSpace : T ⟶ completeIdentityActionAdicChartSpace K n h m i j :=
  pullback.lift x y (by
    rw [← Category.assoc, hx, Category.assoc,
      completeIdentityActionGraphStageOriginalProjection_input_assoc,
      ← completeIdentityActionGraphStageOriginalLift_contraction,
      ← Category.assoc, ← hy, Category.assoc])

/-- The node-pair map retains the full original graph embedding. -/
@[reassoc] theorem completeIdentityGraphChartLiftSpace_embedding :
    completeIdentityGraphChartLiftSpace K n h m i j f x y hx hy ≫ (v) = f ≫ (e) := by
  apply pullback.hom_ext
  · rw [Category.assoc, completeIdentityActionAdicChartSpaceMap_fst,
      completeIdentityGraphChartLiftSpace, pullback.lift_fst_assoc, hx,
      Category.assoc, completeIdentityActionGraphAdicEmbedding_fst]
  · rw [Category.assoc, completeIdentityActionAdicChartSpaceMap_snd,
      completeIdentityGraphChartLiftSpace, pullback.lift_snd_assoc, hy,
      Category.assoc, completeIdentityActionGraphAdicEmbedding_snd]

/-- The unchanged graph chart contains exactly these factorizations of both coordinates. -/
def completeIdentityGraphChartLift : T ⟶ completeIdentityActionGraphAdicChart K n h m i j :=
  pullback.lift f (completeIdentityGraphChartLiftSpace K n h m i j f x y hx hy)
    (completeIdentityGraphChartLiftSpace_embedding K n h m i j f x y hx hy).symm

/-- Chart factorization retains the actual full graph map. -/
@[reassoc] theorem completeIdentityGraphChartLift_inclusion :
    completeIdentityGraphChartLift K n h m i j f x y hx hy ≫
      completeIdentityActionGraphAdicChartInclusion K n h m i j = f :=
  pullback.lift_fst _ _ _

/-- No source coordinate is changed by passing to the literal chart. -/
@[reassoc] theorem completeIdentityGraphChartLift_source :
    completeIdentityGraphChartLift K n h m i j f x y hx hy ≫
      completeIdentityActionGraphAdicChartSource K n h m i j = x := by
  rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.fst _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- No target coordinate is changed by passing to the literal chart. -/
@[reassoc] theorem completeIdentityGraphChartLift_target :
    completeIdentityGraphChartLift K n h m i j f x y hx hy ≫
      completeIdentityActionGraphAdicChartTarget K n h m i j = y := by
  rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_snd _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
