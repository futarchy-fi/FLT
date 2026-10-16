/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityGraphAdicRotatedContraction
public import FLT.Mazur.PolygonCompleteIdentityGraphAdicChart

/-!
# Rotated cubic equations in the original graph node charts

Both cyclic labels change, while the two affine chart morphisms remain
unchanged. This is an equation on the actual graph chart with its full ideal.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
open PolygonInfinitesimal
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeRotation completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  FCurve.ModuleSheafTensor.tensor FCurve.divisorLineBundle
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  (m : ℕ) (i j : Fin n) (b : ZMod n)
local notation "A" => Ring K m
local notation "t" => parameter K m
local notation "s" => completeIdentityActionGraphAdicChartSource K n h m i j
local notation "d" => completeIdentityActionGraphAdicChartTarget K n h m i j
local notation "r" => originalStageToCompatibleProj K n h m
local notation "g" => completePointToIntegralCubic K n h (0 : Fin n)
local notation "a" => completeIdentityActionTarget K n h (0 : Fin n)
local notation "f" => completeIdentityFiniteInput K n h 0 m

/-- The same original node projections satisfy the cyclically shifted cubic equation. -/
@[reassoc] theorem completeIdentityActionGraphAdicChart_rotatedContraction :
    (d) ≫ chart (A) (t) n h (rotateIndex b j) ≫ (r) ≫ (g) =
      (s) ≫ chart (A)[T;T⁻¹] (LaurentPolynomial.C (t)) n h (rotateIndex b i) ≫
        (f) ≫ (a) := by
  have he := congrArg (completeIdentityActionGraphAdicChartInclusion K n h m i j ≫ ·)
    (completeIdentityActionGraphStageOriginalLift_rotatedContraction K n h m b)
  rw [← completeIdentityActionGraphAdicChartTarget_inclusion_assoc,
    ← completeIdentityActionGraphAdicChartSource_inclusion_assoc] at he
  change (d) ≫ chart (A) (t) n h j ≫ rotation (A) (t) n h b ≫ (r) ≫ (g) = _ at he
  simpa only [chart_rotation_assoc] using he

end FLT.Mazur.PolygonInfinitesimalStages
