/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstLocalCubicComparison
public import FLT.Mazur.PolygonStageNodeDescentGeometry

/-!
# Higher parameter-zero local coordinate equality from original cubic comparisons

Adjacent descent transports the original contraction to the first positive
stage. The receiving ring, its nilpotents, and both coordinate values remain intact.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "a" k "," j => PolygonInfinitesimal.chart (Ring K k) (parameter K k) n h j
local notation "r" k => originalStageToCompatibleProj K n h k
local notation "c" => completePointToIntegralCubic K n h i
local notation "p" => Equiv.symm (finRotate n) i

/-- Both coordinates agree in every full parameter-zero local receiving ring at a source node. -/
theorem completePointTopLocalCubic_coordinates (m : ℕ)
    {D : Type} [CommRing D] [IsLocalRing D]
    (f g : ChartRing (parameter K (m + 1)) →+* D)
    (hf : f (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1)))
      (parameter K (m + 1))) = 0)
    (hg : g (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1)))
      (parameter K (m + 1))) = 0)
    (hx : g (leftCoordinate (parameter K (m + 1))) ∈ IsLocalRing.maximalIdeal D)
    (hy : g (rightCoordinate (parameter K (m + 1))) ∈ IsLocalRing.maximalIdeal D)
    (hc : ∀ z : Ring K (m + 1),
      f (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1))) z) =
        g (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1))) z))
    (hl : Spec.map (CommRingCat.ofHom g) ≫ (a (m + 1), i) ≫ (r (m + 1)) ≫ (c) =
      Spec.map (CommRingCat.ofHom f) ≫ (a (m + 1), i) ≫ (r (m + 1)) ≫ (c))
    (hr : Spec.map (CommRingCat.ofHom g) ≫ (a (m + 1), (p)) ≫ (r (m + 1)) ≫ (c) =
      Spec.map (CommRingCat.ofHom f) ≫ (a (m + 1), (p)) ≫ (r (m + 1)) ≫ (c)) :
    f (leftCoordinate (parameter K (m + 1))) = g (leftCoordinate (parameter K (m + 1))) ∧
      f (rightCoordinate (parameter K (m + 1))) =
        g (rightCoordinate (parameter K (m + 1))) := by
  induction m with
  | zero =>
    exact ⟨completePointFirstLocalCubic_left K n h i f g hx hy hc hl,
      completePointFirstLocalCubic_right K n h i f g hx hy hc hr⟩
  | succ m ih =>
    let f' := stageNodeDesc K (m + 1) f hf
    let g' := stageNodeDesc K (m + 1) g hg
    have hx' : g' (leftCoordinate (parameter K (m + 1))) ∈ IsLocalRing.maximalIdeal D := by
      simpa only [g', stageNodeDesc_left] using hx
    have hy' : g' (rightCoordinate (parameter K (m + 1))) ∈ IsLocalRing.maximalIdeal D := by
      simpa only [g', stageNodeDesc_right] using hy
    have hl' : Spec.map (CommRingCat.ofHom g') ≫ (a (m + 1), i) ≫ (r (m + 1)) ≫ (c) =
        Spec.map (CommRingCat.ofHom f') ≫ (a (m + 1), i) ≫ (r (m + 1)) ≫ (c) := by
      simpa only [f', g', stageNodeDesc_toComplete_assoc] using hl
    have hr' : Spec.map (CommRingCat.ofHom g') ≫ (a (m + 1), (p)) ≫ (r (m + 1)) ≫ (c) =
        Spec.map (CommRingCat.ofHom f') ≫ (a (m + 1), (p)) ≫ (r (m + 1)) ≫ (c) := by
      simpa only [f', g', stageNodeDesc_toComplete_assoc] using hr
    have he := ih f' g' (stageNodeDesc_parameter K (m + 1) f hf)
      (stageNodeDesc_parameter K (m + 1) g hg) hx' hy'
      (stageNodeDesc_coefficients K (m + 1) f g hf hg hc) hl' hr'
    simpa only [f', g', stageNodeDesc_left, stageNodeDesc_right] using he

end FLT.Mazur.PolygonInfinitesimalStages
