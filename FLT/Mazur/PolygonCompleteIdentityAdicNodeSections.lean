/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicGraphSections
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# The original whole-node sections land in the literal diagonal graph charts

At every finite order and every node label, the original graph section
retains both original node coordinates. The source is the identity and the
target is universal reciprocal scaling, before taking any schematic image.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i : Fin n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => PolygonInfinitesimal.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h i
local notation "d" => PolygonInfinitesimal.chart (A) (t) n h i
local notation "σ" => Spec.map (CommRingCat.ofHom (universalReciprocalScale (t)))
local notation "v" => completeIdentityActionAdicChartSpaceMap K n h m i i
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m
local notation "f" => completeIdentityAdicGraphSection K n h m

/-- The two actual original node coordinates satisfy the whole cubic relation. -/
def completeIdentityAdicNodeSectionSpace :
    PolygonSmoothing.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) ⟶
      completeIdentityActionAdicChartSpace K n h m i i :=
  pullback.lift (𝟙 _) (σ) (by
    rw [Category.id_comp]
    have he := congrArg ((s) ≫ ·) (completeIdentityFiniteComparison_all K n h m)
    rw [← Category.assoc, completeIdentityFiniteScaling,
      chart_universalScaling_assoc] at he
    simpa only [Category.assoc] using he.symm)

/-- The full node relation is the image of the unchanged whole-input graph section. -/
@[reassoc] theorem completeIdentityAdicNodeSectionSpace_graph :
    completeIdentityAdicNodeSectionSpace K n h m i ≫ (v) = (s) ≫ (f) ≫ (e) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_fst,
      completeIdentityAdicNodeSectionSpace, pullback.lift_fst_assoc, Category.id_comp,
      completeIdentityActionGraphAdicEmbedding_fst,
      completeIdentityAdicGraphSection_projection, Category.comp_id]
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_snd,
      completeIdentityAdicNodeSectionSpace, pullback.lift_snd_assoc,
      completeIdentityActionGraphAdicEmbedding_snd, completeIdentityAdicGraphSection_target]
    exact (chart_universalScaling (A) (t) n h i).symm

/-- Every full original node has a section in the literal same-label graph chart. -/
def completeIdentityAdicNodeSection :
    PolygonSmoothing.chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) ⟶
      completeIdentityActionGraphAdicChart K n h m i i :=
  pullback.lift ((s) ≫ (f)) (completeIdentityAdicNodeSectionSpace K n h m i)
    (by simpa only [Category.assoc] using
      (completeIdentityAdicNodeSectionSpace_graph K n h m i).symm)

/-- The section is exactly the original whole-input map on this node. -/
@[reassoc] theorem completeIdentityAdicNodeSection_inclusion :
    completeIdentityAdicNodeSection K n h m i ≫
      completeIdentityActionGraphAdicChartInclusion K n h m i i = (s) ≫ (f) :=
  pullback.lift_fst _ _ _

/-- Every original node coordinate survives the full graph projection unchanged. -/
@[reassoc] theorem completeIdentityAdicNodeSection_source :
    completeIdentityAdicNodeSection K n h m i ≫
      completeIdentityActionGraphAdicChartSource K n h m i i = 𝟙 _ := by
  rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.fst _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- The original target node coordinate is the prescribed full universal scaling. -/
@[reassoc] theorem completeIdentityAdicNodeSection_target :
    completeIdentityAdicNodeSection K n h m i ≫
      completeIdentityActionGraphAdicChartTarget K n h m i i = (σ) := by
  rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_snd _ _ _

end FLT.Mazur.PolygonInfinitesimalStages
