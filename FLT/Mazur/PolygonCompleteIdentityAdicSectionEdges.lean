/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicSectionChartCoverage
public import FLT.Mazur.PolygonCompleteIdentityGraphRotatedEdgeCartesian

/-!
# The original section contains every graph point over a punctured edge

The full graph preimage of each original source edge equals the edge in the
constructed section. Thus the residual clopen complement has no smooth edge inputs.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonInfinitesimal PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "j" => edge (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b 0)
local notation "o" => completeIdentityActionInputStageOriginalIso K n h m
local notation "v" => completeIdentityRotatedEdgeToAdicGraph K n h m b
local notation "p" => completeIdentityActionGraphStageOriginalProjection K n h m

/-- The constructed edge is exactly the restriction of the whole original section. -/
@[reassoc] theorem completeIdentityAdicGraphSection_edge :
    (j) ≫ completeIdentityAdicGraphSection K n h m = (v) := by
  apply completeIdentityRotatedEdgeToAdicGraph_unique K n h m b _ (𝟙 _)
  have he : (j) ≫ completeIdentityAdicGraphSection K n h m ≫ (p) = (j) := by
    rw [completeIdentityAdicGraphSection_projection, Category.comp_id]
  have hh := congrArg (fun f ↦ f ≫ (o).hom) he
  simpa only [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Category.id_comp] using hh

/-- The edge square is Cartesian for the original, unaltered input projection. -/
theorem completeIdentityAdicOriginalEdge_isPullback :
    IsPullback (v) (𝟙 _) (p) (j) := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (by
      change (v) ≫ (p) = 𝟙 _ ≫ (j)
      rw [completeIdentityRotatedEdgeToAdicGraph_source, Category.id_comp])
    (fun c ↦ c.snd) ?_ ?_ ?_)
  · intro c
    apply Eq.symm
    apply completeIdentityRotatedEdgeToAdicGraph_unique K n h m b
    have hh := congrArg (fun f ↦ f ≫ (o).hom) c.condition
    simpa only [completeIdentityActionGraphStageOriginalProjection, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using hh
  · intro c
    exact Category.comp_id _
  · intro c k _ hk
    simpa only [Category.comp_id] using hk

/-- The full set-theoretic preimage of each edge is its actual original graph edge. -/
theorem completeIdentityAdicOriginalEdge_range :
    Set.range (v) = (p) ⁻¹' Set.range (j) := by
  have hp := completeIdentityAdicOriginalEdge_isPullback K n h m b
  rw [← hp.isoPullback_hom_fst]
  change Set.range ((pullback.fst (p) (j)) ∘ hp.isoPullback.hom) = _
  exact (hp.isoPullback.hom.homeomorph.surjective.range_comp _).trans
    (Scheme.Pullback.range_fst _ _)

/-- Every positive-order graph point over any original edge lies in the section open. -/
theorem completeIdentityAdicSectionOpen_of_edge
    (i : Fin n) (x : completeIdentityActionGraphStage K n h (m + 1))
    (hx : completeIdentityActionGraphStageOriginalProjection K n h (m + 1) x ∈
      Set.range (edge (Ring K (m + 1))[T;T⁻¹]
        (LaurentPolynomial.C (parameter K (m + 1))) n h i)) :
    x ∈ completeIdentityAdicSectionOpen K n h m := by
  have hi : rotateIndex (ZMod.finEquiv n i) (0 : Fin n) = i := by
    simp only [rotateIndex, map_zero, zero_add, RingEquiv.symm_apply_apply]
  have hr := completeIdentityAdicOriginalEdge_range K n h (m + 1) (ZMod.finEquiv n i)
  rw [hi] at hr
  have hx' : x ∈ Set.range
      (completeIdentityRotatedEdgeToAdicGraph K n h (m + 1) (ZMod.finEquiv n i)) := by
    rw [hr]
    exact hx
  obtain ⟨z, rfl⟩ := hx'
  change _ ∈ (completeIdentityAdicSectionOpen K n h m :
    Set (completeIdentityActionGraphStage K n h (m + 1)))
  rw [← completeIdentityAdicGraphSection_edge, completeIdentityAdicSectionOpen_carrier]
  exact ⟨_, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
