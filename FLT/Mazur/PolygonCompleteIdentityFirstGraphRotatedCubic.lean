/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphChartRotatedContraction
public import FLT.Mazur.PolygonCompleteIdentityFirstSourceZeroCubic

/-!
# Parameter-zero rotated cubic comparison on the full original graph

The order-zero action law and the complete graph's rotated equations compare
actual target coordinates with reciprocal scaling of actual source coordinates.
Every receiving ring may have arbitrary nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
open PolygonInfinitesimal PolygonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (i j : Fin n) (b : ZMod n)
local notation "A" => Ring K 1
local notation "t" => parameter K 1
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "r" => originalStageToCompatibleProj K n h 1
variable {B : Type} [CommRing B]
variable (w : Spec (.of B) ⟶ completeIdentityActionGraphAdicChart K n h 1 i j)
variable (σ : ChartRing (LaurentPolynomial.C (parameter K 1)) →+* B)
variable (hs : w ≫ completeIdentityActionGraphAdicChartSource K n h 1 i j =
  Spec.map (CommRingCat.ofHom σ))
variable (ht : σ (algebraMap (Ring K 1)[T;T⁻¹]
  (ChartRing (LaurentPolynomial.C (parameter K 1)))
    (LaurentPolynomial.C (parameter K 1))) = 0)

include hs ht

/-- The full original graph identifies the rotated target cubic with the scaled source cubic. -/
theorem completeIdentityFirstGraph_rotatedCubic :
    w ≫ completeIdentityActionGraphAdicChartTarget K n h 1 i j ≫
        PolygonInfinitesimal.chart (A) (t) n h (rotateIndex b j) ≫ (r) ≫ (g) =
      Spec.map (CommRingCat.ofHom (σ.comp (universalReciprocalScale (t)))) ≫
        PolygonInfinitesimal.chart (A) (t) n h (rotateIndex b i) ≫ (r) ≫ (g) := by
  rw [completeIdentityActionGraphAdicChart_rotatedContraction,
    ← Category.assoc w, hs,
    ← completeIdentityFirstSource_cubic_of_parameter_zero K n h (rotateIndex b i) σ ht]
  simp only [completeIdentityFiniteScaling, Category.assoc, chart_universalScaling_assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]

end FLT.Mazur.PolygonInfinitesimalStages
