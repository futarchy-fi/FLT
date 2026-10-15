/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicRotatedEdge
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# The actual incoming edge in the original node-pair graph chart

Use the adjacent component's original smooth multiplication and the original
atlas overlap. Both full node coordinates land in the preceding diagonal
chart of the literal adic graph, with no reduction or radical operation.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonSmoothing PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "i" => Equiv.symm (finRotate n) (rotateIndex b (0 : Fin n))
local notation "M" => completeIdentityFiniteMulCoordinates K n h 0 m
local notation "l" => precedingBranch (A)[T;T⁻¹] (LaurentPolynomial.C (t))
local notation "r" => precedingBranch (A) (t)
local notation "f" => completeIdentityRotatedEdgeToAdicGraph K n h m b
local notation "v" => completeIdentityActionAdicChartSpaceMap K n h m (i) (i)
local notation "e" => completeIdentityActionGraphAdicEmbedding K n h m

/-- The original incoming pair satisfies the full original cubic equation on its node charts. -/
def completeIdentityIncomingToChartSpace :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionAdicChartSpace K n h m (i) (i) :=
  pullback.lift (l) ((M) ≫ (r)) (by
    have he := completeIdentityFiniteOriginalMul_rotatedCubic K n h m b
    rw [← completeIdentityFiniteMulCoordinates_original,
      Category.assoc, completeIdentityStageEdge_rotation_assoc] at he
    simpa only [edge, Category.assoc, overlap_assoc] using he.symm)

/-- The incoming pair lies in the actual graph, rather than just the ambient cubic relation. -/
@[reassoc] theorem completeIdentityIncomingToChartSpace_graph :
    completeIdentityIncomingToChartSpace K n h m b ≫ (v) = (f) ≫ (e) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_fst,
      completeIdentityIncomingToChartSpace, pullback.lift_fst_assoc,
      completeIdentityActionGraphAdicEmbedding_fst,
      completeIdentityRotatedEdgeToAdicGraph_source]
    exact (overlap (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)).symm
  · simp only [Category.assoc, completeIdentityActionAdicChartSpaceMap_snd,
      completeIdentityIncomingToChartSpace, pullback.lift_snd_assoc,
      completeIdentityActionGraphAdicEmbedding_snd,
      completeIdentityRotatedEdgeToAdicGraph_target, edge, overlap]

/-- The full incoming edge belongs to the original preceding diagonal node-pair graph chart. -/
def completeIdentityIncomingToGraphChart :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphAdicChart K n h m (i) (i) :=
  pullback.lift (f) (completeIdentityIncomingToChartSpace K n h m b)
    (completeIdentityIncomingToChartSpace_graph K n h m b).symm

/-- The chart inclusion recovers exactly the rotated original graph edge. -/
@[reassoc] theorem completeIdentityIncomingToGraphChart_inclusion :
    completeIdentityIncomingToGraphChart K n h m b ≫
      completeIdentityActionGraphAdicChartInclusion K n h m (i) (i) = (f) :=
  pullback.lift_fst _ _ _

/-- The entire original source node coordinate is the incoming atlas puncture. -/
@[reassoc] theorem completeIdentityIncomingToGraphChart_source :
    completeIdentityIncomingToGraphChart K n h m b ≫
      completeIdentityActionGraphAdicChartSource K n h m (i) (i) = (l) := by
  rw [completeIdentityActionGraphAdicChartSource, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.fst _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_fst _ _ _

/-- The entire target node coordinate is original multiplication in the incoming puncture. -/
@[reassoc] theorem completeIdentityIncomingToGraphChart_target :
    completeIdentityIncomingToGraphChart K n h m b ≫
      completeIdentityActionGraphAdicChartTarget K n h m (i) (i) = (M) ≫ (r) := by
  rw [completeIdentityActionGraphAdicChartTarget, ← Category.assoc]
  change (pullback.lift _ _ _ ≫ pullback.snd _ _) ≫ pullback.snd _ _ = _
  rw [pullback.lift_snd]
  exact pullback.lift_snd _ _ _

/-- Label the incoming chart by an equal original index without changing its morphism. -/
def completeIdentityIncomingToGraphChartAt (j : Fin n) (hj : (i) = j) :
    branchTorus (A)[T;T⁻¹] ⟶ completeIdentityActionGraphAdicChart K n h m j j := by
  subst j
  exact completeIdentityIncomingToGraphChart K n h m b

/-- Reindexing retains the entire original incoming source node. -/
@[reassoc] theorem completeIdentityIncomingToGraphChartAt_source
    (j : Fin n) (hj : (i) = j) :
    completeIdentityIncomingToGraphChartAt K n h m b j hj ≫
      completeIdentityActionGraphAdicChartSource K n h m j j = (l) := by
  subst j
  exact completeIdentityIncomingToGraphChart_source K n h m b

/-- Reindexing retains original multiplication and the full incoming target node. -/
@[reassoc] theorem completeIdentityIncomingToGraphChartAt_target
    (j : Fin n) (hj : (i) = j) :
    completeIdentityIncomingToGraphChartAt K n h m b j hj ≫
      completeIdentityActionGraphAdicChartTarget K n h m j j = (M) ≫ (r) := by
  subst j
  exact completeIdentityIncomingToGraphChart_target K n h m b

end FLT.Mazur.PolygonInfinitesimalStages
