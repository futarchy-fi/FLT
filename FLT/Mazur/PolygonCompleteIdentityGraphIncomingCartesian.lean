/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphRotatedEdgeCartesian
public import FLT.Mazur.PolygonCompleteIdentityGraphIncomingChart

/-!
# The full incoming puncture of the original adic node-pair chart

Every chart-valued family whose source lies on the incoming puncture is
the original constructed edge family. This gives its full Cartesian
preimage and open immersion, including all nilpotent coefficients.
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
local notation "ix" => Equiv.symm (finRotate n) (rotateIndex b (0 : Fin n))
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "U" => branchTorus (A)[T;T⁻¹]
local notation "H" => completeIdentityActionGraphAdicChart K n h m (ix) (ix)
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "l" => precedingBranch (A)[T;T⁻¹] (LaurentPolynomial.C (t))
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)
local notation "v" => completeIdentityIncomingToGraphChart K n h m b
local notation "s" => completeIdentityActionGraphAdicChartSource K n h m (ix) (ix)
local notation "i" => completeIdentityActionGraphAdicChartInclusion K n h m (ix) (ix)

/-- All original graph-chart families over the incoming source edge are the original edge lift. -/
theorem completeIdentityIncomingToGraphChart_unique {T : Scheme}
    (g : T ⟶ (H)) (a : T ⟶ (U)) (he : g ≫ (s) = a ≫ (l)) : g = a ≫ (v) := by
  apply (cancel_mono (i)).mp
  rw [Category.assoc, completeIdentityIncomingToGraphChart_inclusion]
  apply completeIdentityRotatedEdgeToAdicGraph_unique K n h m b
  have hs : g ≫ (i) ≫ completeIdentityActionGraphStageOriginalProjection K n h m =
      a ≫ (j) := by
    rw [← completeIdentityActionGraphAdicChartSource_inclusion, ← Category.assoc, he,
      Category.assoc]
    rw [← overlap]
    rfl
  have hh := congrArg (fun u ↦ u ≫ (o).hom) hs
  simpa only [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

/-- The incoming chart branch is the full scheme-theoretic inverse image of its source puncture. -/
theorem completeIdentityIncomingToGraphChart_isPullback :
    IsPullback (v) (𝟙 (U)) (s) (l) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by
      change (v) ≫ (s) = 𝟙 (U) ≫ (l)
      rw [completeIdentityIncomingToGraphChart_source, Category.id_comp])
    (fun c ↦ c.snd) ?_ ?_ ?_)
  · intro c
    exact (completeIdentityIncomingToGraphChart_unique
      K n h m b c.fst c.snd c.condition).symm
  · intro c
    exact Category.comp_id _
  · intro c u _ hk
    simpa only [Category.comp_id] using hk

/-- The full incoming puncture is an actual open subscheme of the unchanged adic chart. -/
instance completeIdentityIncomingToGraphChart_open : IsOpenImmersion (v) :=
  MorphismProperty.of_isPullback
    (completeIdentityIncomingToGraphChart_isPullback K n h m b).flip inferInstance

/-- Changing an equal chart label retains the full incoming Cartesian square. -/
theorem completeIdentityIncomingToGraphChartAt_isPullback
    (jj : Fin n) (hj : (ix) = jj) :
    IsPullback (completeIdentityIncomingToGraphChartAt K n h m b jj hj) (𝟙 (U))
      (completeIdentityActionGraphAdicChartSource K n h m jj jj) (l) := by
  subst jj
  exact completeIdentityIncomingToGraphChart_isPullback K n h m b

/-- The reindexed incoming morphism is still the full open puncture. -/
instance completeIdentityIncomingToGraphChartAt_open (jj : Fin n) (hj : (ix) = jj) :
    IsOpenImmersion (completeIdentityIncomingToGraphChartAt K n h m b jj hj) :=
  MorphismProperty.of_isPullback
    (completeIdentityIncomingToGraphChartAt_isPullback K n h m b jj hj).flip inferInstance

end FLT.Mazur.PolygonInfinitesimalStages
