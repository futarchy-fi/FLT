/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointGenericCubicIso
public import FLT.Mazur.PolygonCompletePointGlobalFunctions
public import FLT.Mazur.CartesianFiniteFibers
public import FLT.Mazur.ProperFunctionSheafIso

/-!
# Unchanged neighborhoods above nonzero-parameter residue fibers

The original field comparison supplies finite fibers of the full contraction.
The function-sheaf comparison then spreads the actual isomorphism to an open
neighborhood in the original complete-base cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (L : Type) [Field L] (a : PowerSeries K →+* L) (ha : a PowerSeries.X ≠ 0)
  [IsPreimmersion (Spec.map (CommRingCat.ofHom a))]
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "s" => Spec.map (CommRingCat.ofHom a)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "b" => pullback.fst (integralCurveStructure (W)) (s ≫ Scheme.toSpecΓ (S₀))
local notation "f" => exactVeroneseProjToBase K n h

include ha in
/-- Every point of the actual nonzero-parameter residue cubic has finite original fiber. -/
theorem completePointToIntegralCubic_finite_fiber_generic
    (y : completePointCubicBaseChange K n h s i) : ((g) ⁻¹' {(b) y}).Finite := by
  let p := pullback.fst (f) (s)
  let q := pullback.snd (f) (s)
  let H := IsPullback.of_hasPullback (f) (s)
  let v := completePointToCubicBaseChange K n h s p q H i
  let _ := completePointToCubicBaseChange_isIso_of_parameter_ne_zero K n h L a ha p q H i
  apply CartesianFiniteFibers.finite_fiber
    (completePointToCubicBaseChange_isPullback K n h s p q H i) (b).isEmbedding.injective
  exact Set.Finite.preimage (ConcreteCategory.bijective_of_isIso v.base).injective.injOn
    (Set.finite_singleton y)

include ha in
/-- The actual generic comparison extends to an unchanged open of the original cubic. -/
theorem completePointToIntegralCubic_exists_isIso_generic
    (y : completePointCubicBaseChange K n h s i) :
    ∃ U : (integralCurve (W)).Opens, (b) y ∈ U ∧ IsIso ((g) ∣_ U) := by
  let _ := completePointToIntegralCubic_proper K n h i
  exact ProperFunctionSheafIso.exists_isIso_neighborhood (g)
    (completePointToIntegralCubic_app_isIso K n h i) _
    (completePointToIntegralCubic_finite_fiber_generic K n h i L a ha y)

end FLT.Mazur.PolygonInfinitesimalStages
