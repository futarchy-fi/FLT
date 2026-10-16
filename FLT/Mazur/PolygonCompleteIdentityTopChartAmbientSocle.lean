/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopChartClosedPresentation
public import FLT.Mazur.PolygonCompleteIdentityTopChartFiberSocle

/-!
# Exact ambient ideal test for original higher-node preservation

The closed-fiber common annihilator is expressed by multiplication into the
full graph-plus-parameter ideal. This retains every nilpotent in the
literal closed chart. The ideal membership test remains to be established.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityTopActionUnit completeIdentityTopActionField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ)
local notation "e" => parameter K[T;T⁻¹] (m + 1)
local notation "R" => completeIdentityActionAdicChartSpace K n h (m + 1) 0 0
local notation "s" => completeIdentityTopAmbientSourceFunctions K n h m
local notation "f" => completeIdentityTopChartClosedAmbientMap K n h m
local notation "J" => completeIdentityTopChartClosedAmbientIdeal K n h m
local notation "q" => completeIdentityTopChartClosedQuotient K n h m
local notation "x" => completeIdentityTopChartSourceX K n h m
local notation "y" => completeIdentityTopChartSourceY K n h m

/-- The original left-coordinate annihilator is precisely an ambient ideal membership test. -/
theorem completeIdentityTopChartAmbientSocle_left (z : Γ((R), ⊤)) :
    (q) (x) * (f) z = 0 ↔ (s) (leftCoordinate (e)) * z ∈ (J) := by
  have he : (f) ((s) (leftCoordinate (e))) = (q) (x) := by
    change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).appTop
      ((s) (leftCoordinate (e)))) = _
    rw [completeIdentityTopAmbientSourceFunctions_restrict]
    rfl
  rw [← he, ← map_mul, completeIdentityTopChartClosedAmbientMap_eq_zero]

/-- The original right-coordinate annihilator uses the same full ambient ideal. -/
theorem completeIdentityTopChartAmbientSocle_right (z : Γ((R), ⊤)) :
    (q) (y) * (f) z = 0 ↔ (s) (rightCoordinate (e)) * z ∈ (J) := by
  have he : (f) ((s) (rightCoordinate (e))) = (q) (y) := by
    change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h (m + 1) 0 0).appTop
      ((s) (rightCoordinate (e)))) = _
    rw [completeIdentityTopAmbientSourceFunctions_restrict]
    rfl
  rw [← he, ← map_mul, completeIdentityTopChartClosedAmbientMap_eq_zero]

/-- The entire comparison kernel vanishes exactly when the full ambient ideal has no node socle. -/
theorem completeIdentityTopChartNodeKernel_eq_bot_iff_ambientSocle :
    completeIdentityTopChartNodeKernel K n h m = ⊥ ↔
      ∀ z : Γ((R), ⊤), (s) (leftCoordinate (e)) * z ∈ (J) →
        (s) (rightCoordinate (e)) * z ∈ (J) → z ∈ (J) := by
  rw [completeIdentityTopChartNodeKernel_eq_bot_iff_closedSocle]
  constructor
  · intro hs z hx hy
    exact (completeIdentityTopChartClosedAmbientMap_eq_zero K n h m z).mp
      (hs ((f) z) ((completeIdentityTopChartAmbientSocle_left K n h m z).mpr hx)
        ((completeIdentityTopChartAmbientSocle_right K n h m z).mpr hy))
  · intro hs z hx hy
    obtain ⟨w, rfl⟩ := completeIdentityTopChartClosedAmbientMap_surjective K n h m z
    exact (completeIdentityTopChartClosedAmbientMap_eq_zero K n h m w).mpr
      (hs w ((completeIdentityTopChartAmbientSocle_left K n h m w).mp hx)
        ((completeIdentityTopChartAmbientSocle_right K n h m w).mp hy))

end FLT.Mazur.PolygonInfinitesimalStages
