/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphEdgeCartesian
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChartEdge

/-!
# The full outgoing puncture of the original adic node-pair chart

Every chart-valued family whose source lies on the outgoing puncture is
the original constructed edge family. This gives its full Cartesian
preimage and open immersion, including all nilpotent coefficients.
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
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "U" => branchTorus (A)[T;T⁻¹]
local notation "H" => completeIdentityActionGraphAdicChart K n h m 0 0
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "l" => leftBranchOpen (A)[T;T⁻¹] (LaurentPolynomial.C (t))
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (0 : Fin n)
local notation "v" => completeIdentityFiniteEdgeToGraphChart K n h m
local notation "s" => completeIdentityActionGraphAdicChartSource K n h m 0 0
local notation "i" => completeIdentityActionGraphAdicChartInclusion K n h m 0 0

/-- All original graph-chart families over the outgoing source edge are the original edge lift. -/
theorem completeIdentityFiniteEdgeToGraphChart_unique {T : Scheme}
    (g : T ⟶ (H)) (a : T ⟶ (U)) (he : g ≫ (s) = a ≫ (l)) : g = a ≫ (v) := by
  apply (cancel_mono (i)).mp
  rw [Category.assoc, completeIdentityFiniteEdgeToGraphChart_inclusion]
  apply completeIdentityFiniteEdgeToAdicGraph_unique K n h m
  have hs : g ≫ (i) ≫ completeIdentityActionGraphStageOriginalProjection K n h m =
      a ≫ (j) := by
    rw [← completeIdentityActionGraphAdicChartSource_inclusion, ← Category.assoc, he,
      Category.assoc]
    rfl
  have hh := congrArg (fun k ↦ k ≫ (o).hom) hs
  simpa only [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using hh

/-- The outgoing chart branch is the full scheme-theoretic inverse image of its source puncture. -/
theorem completeIdentityFiniteEdgeToGraphChart_isPullback :
    IsPullback (v) (𝟙 (U)) (s) (l) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by
      change (v) ≫ (s) = 𝟙 (U) ≫ (l)
      rw [completeIdentityFiniteEdgeToGraphChart_source, Category.id_comp])
    (fun c ↦ c.snd) ?_ ?_ ?_)
  · intro c
    exact (completeIdentityFiniteEdgeToGraphChart_unique K n h m c.fst c.snd c.condition).symm
  · intro c
    exact Category.comp_id _
  · intro c k _ hk
    simpa only [Category.comp_id] using hk

/-- The full outgoing puncture is an actual open subscheme of the unchanged adic chart. -/
instance completeIdentityFiniteEdgeToGraphChart_open : IsOpenImmersion (v) :=
  MorphismProperty.of_isPullback
    (completeIdentityFiniteEdgeToGraphChart_isPullback K n h m).flip inferInstance

end FLT.Mazur.PolygonInfinitesimalStages
