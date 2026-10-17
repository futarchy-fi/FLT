/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonStageNodeParameterDescent
public import FLT.Mazur.PolygonCompleteIdentityFiniteCoherence

/-!
# Original contraction and coefficients survive parameter-zero node descent

Adjacent descent changes only the stage through which a receiving map factors.
It preserves the original complete contraction and equality of base coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "t" => parameter K (m + 1)
local notation "s" => parameter K m
local notation "a" k "," j => PolygonInfinitesimal.chart (Ring K k) (parameter K k) n h j

omit [NeZero n] in
/-- The original adjacent node restriction is the chart of the actual family restriction. -/
@[reassoc] theorem stageNodeRestriction_chart (j : Fin n) :
    Spec.map (CommRingCat.ofHom (stageNodeRestriction K m)) ≫ (a (m + 1), j) =
      (a m, j) ≫ stageRestriction K m n h := by
  rw [stageRestriction, chart_parameterProjection]
  rfl

/-- The node restriction retains the original complete-stage realization. -/
@[reassoc] theorem stageNodeRestriction_toComplete (j : Fin n) :
    Spec.map (CommRingCat.ofHom (stageNodeRestriction K m)) ≫ (a (m + 1), j) ≫
        originalStageToCompatibleProj K n h (m + 1) =
      (a m, j) ≫ originalStageToCompatibleProj K n h m := by
  rw [stageNodeRestriction_chart_assoc, completeIdentityStageRestriction_toComplete]

variable {D : Type} [CommRing D] (f g : ChartRing (parameter K (m + 1)) →+* D)
variable (hf : f (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1)))
  (parameter K (m + 1))) = 0)
variable (hg : g (algebraMap (Ring K (m + 1)) (ChartRing (parameter K (m + 1)))
  (parameter K (m + 1))) = 0)

/-- Descent preserves the original full complete contraction on every chart. -/
@[reassoc] theorem stageNodeDesc_toComplete (j : Fin n) :
    Spec.map (CommRingCat.ofHom (stageNodeDesc K m f hf)) ≫ (a m, j) ≫
        originalStageToCompatibleProj K n h m =
      Spec.map (CommRingCat.ofHom f) ≫ (a (m + 1), j) ≫
        originalStageToCompatibleProj K n h (m + 1) := by
  rw [← stageNodeRestriction_toComplete K n h m j]
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, stageNodeDesc_comp]

omit [NeZero n] in
/-- Equality of original coefficients descends through the surjective base restriction. -/
theorem stageNodeDesc_coefficients
    (hc : ∀ c : Ring K (m + 1),
      f (algebraMap (Ring K (m + 1)) (ChartRing (t)) c) =
        g (algebraMap (Ring K (m + 1)) (ChartRing (t)) c)) (c : Ring K m) :
    stageNodeDesc K m f hf (algebraMap (Ring K m) (ChartRing (s)) c) =
      stageNodeDesc K m g hg (algebraMap (Ring K m) (ChartRing (s)) c) := by
  obtain ⟨c, rfl⟩ := restriction_surjective K m c
  have hfc := RingHom.congr_fun (stageNodeDesc_comp K m f hf)
    (algebraMap (Ring K (m + 1)) (ChartRing (t)) c)
  have hgc := RingHom.congr_fun (stageNodeDesc_comp K m g hg)
    (algebraMap (Ring K (m + 1)) (ChartRing (t)) c)
  simp only [RingHom.comp_apply, stageNodeRestriction, ringMap_scalar] at hfc hgc
  exact hfc.trans ((hc c).trans hgc.symm)

end FLT.Mazur.PolygonInfinitesimalStages
