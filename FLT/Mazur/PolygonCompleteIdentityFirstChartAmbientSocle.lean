/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstChartResidualPresentation
public import FLT.Mazur.PolygonCompleteIdentityFirstChartFiberSocle

/-!
# Exact ambient ideal test for original first-node preservation

The closed-fiber common annihilator is expressed by multiplication into the
full graph-plus-parameter ideal. Its representatives automatically lie in
the original ambient node kernel. The ideal test remains to be established.
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
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "e" => parameter K[T;T⁻¹] 1
local notation "R" => completeIdentityActionAdicChartSpace K n h 1 0 0
local notation "s" => completeIdentityFirstAmbientSourceFunctions K n h
local notation "f" => completeIdentityFirstChartClosedAmbientMap K n h
local notation "J" => completeIdentityFirstChartClosedAmbientIdeal K n h
local notation "q" => completeIdentityFirstChartClosedQuotient K n h
local notation "x" => completeIdentityFirstChartSourceX K n h
local notation "y" => completeIdentityFirstChartSourceY K n h

/-- The original left-coordinate annihilator is precisely an ambient ideal membership test. -/
theorem completeIdentityFirstChartAmbientSocle_left (z : Γ((R), ⊤)) :
    (q) (x) * (f) z = 0 ↔ (s) (leftCoordinate (e)) * z ∈ (J) := by
  have he : (f) ((s) (leftCoordinate (e))) = (q) (x) := by
    change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).appTop
      ((s) (leftCoordinate (e)))) = _
    rw [completeIdentityFirstAmbientSourceFunctions_restrict]
    rfl
  rw [← he, ← map_mul, completeIdentityFirstChartClosedAmbientMap_eq_zero]

/-- The original right-coordinate annihilator uses the same full ambient ideal. -/
theorem completeIdentityFirstChartAmbientSocle_right (z : Γ((R), ⊤)) :
    (q) (y) * (f) z = 0 ↔ (s) (rightCoordinate (e)) * z ∈ (J) := by
  have he : (f) ((s) (rightCoordinate (e))) = (q) (y) := by
    change (q) ((completeIdentityActionGraphAdicChartEmbedding K n h 1 0 0).appTop
      ((s) (rightCoordinate (e)))) = _
    rw [completeIdentityFirstAmbientSourceFunctions_restrict]
    rfl
  rw [← he, ← map_mul, completeIdentityFirstChartClosedAmbientMap_eq_zero]

/-- Every ambient common annihilator already belongs to the full original node kernel. -/
theorem completeIdentityFirstChartAmbientSocle_nodeKernel (z : Γ((R), ⊤))
    (hx : (s) (leftCoordinate (e)) * z ∈ (J))
    (hy : (s) (rightCoordinate (e)) * z ∈ (J)) :
    completeIdentityFirstAmbientNodeReduction K n h z = 0 :=
  completeIdentityFirstChartClosedSocle_reduction K n h ((f) z)
    ((completeIdentityFirstChartAmbientSocle_left K n h z).mpr hx)
    ((completeIdentityFirstChartAmbientSocle_right K n h z).mpr hy)

/-- The entire comparison kernel vanishes exactly when the full ambient ideal has no node socle. -/
theorem completeIdentityFirstChartNodeKernel_eq_bot_iff_ambientSocle :
    completeIdentityFirstChartNodeKernel K n h = ⊥ ↔
      ∀ z : Γ((R), ⊤), (s) (leftCoordinate (e)) * z ∈ (J) →
        (s) (rightCoordinate (e)) * z ∈ (J) → z ∈ (J) := by
  rw [completeIdentityFirstChartNodeKernel_eq_bot_iff_closedSocle]
  constructor
  · intro hs z hx hy
    exact (completeIdentityFirstChartClosedAmbientMap_eq_zero K n h z).mp
      (hs ((f) z) ((completeIdentityFirstChartAmbientSocle_left K n h z).mpr hx)
        ((completeIdentityFirstChartAmbientSocle_right K n h z).mpr hy))
  · intro hs z hx hy
    obtain ⟨w, rfl⟩ := completeIdentityFirstChartClosedAmbientMap_surjective K n h z
    exact (completeIdentityFirstChartClosedAmbientMap_eq_zero K n h w).mpr
      (hs w ((completeIdentityFirstChartAmbientSocle_left K n h w).mp hx)
        ((completeIdentityFirstChartAmbientSocle_right K n h w).mp hy))

end FLT.Mazur.PolygonInfinitesimalStages
