/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityTopObstruction

/-!
# Both identity slices of the original obstruction vanish

The original unit laws kill both slices of the exact multiplication error.
The canonical reduced obstruction inherits this normalization when the
preceding law holds, using injectivity of the top-layer scalar embedding.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" j => Ring K j
local notation "δ" j => completeIdentityFiniteMulDefect K n h i j
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "ε" S => AlgHom.toRingHom (LaurentUnitPoints.evalUnit (R := S) (1 : Sˣ))

/-- The actual full error vanishes when its first Laurent input is the identity. -/
theorem completeIdentityFiniteMulDefect_firstUnit : coeffMap (ε (A m)) (δ m) = 0 := by
  have he := congrArg Units.val (completeIdentityFiniteMulUnit_firstUnit K n h i m)
  change coeffMap (ε (A m)) _ = _ at he
  rw [completeIdentityFiniteMulDefect, map_sub, he]
  simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit,
    LaurentUnitPoints.evalUnit_T]

/-- The actual full error vanishes when its second Laurent input is the identity. -/
theorem completeIdentityFiniteMulDefect_secondUnit : (ε (A m)[T;T⁻¹]) (δ m) = 0 := by
  have he := congrArg Units.val (completeIdentityFiniteMulUnit_secondUnit K n h i m)
  change (ε (A m)[T;T⁻¹]) _ = _ at he
  rw [completeIdentityFiniteMulDefect, map_sub, he]
  simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit,
    LaurentUnitPoints.evalUnit_C, LaurentUnitPoints.evalUnit_T]

/-- The canonical top obstruction retains the first identity normalization. -/
theorem completeIdentityFiniteMulObstruction_firstUnit (hm : (δ m) = 0) :
    coeffMap (ε K) (O) = 0 := by
  apply (laurent_top_lift_eq_zero_iff K (m + 1) _).mp
  have he := completeIdentityFiniteMulDefect_firstUnit K n h i (m + 1)
  rw [completeIdentityFiniteMulDefect_from_obstruction K n h i m hm,
    map_mul, map_pow, coeffMap_C] at he
  have hc : (ε (A (m + 1))) (C (parameter K (m + 1))) = parameter K (m + 1) := by
    change LaurentUnitPoints.evalUnit (R := A (m + 1)) (1 : (A (m + 1))ˣ) _ = _
    exact LaurentUnitPoints.evalUnit_C _ _
  rw [hc] at he
  rw [← RingHom.comp_apply,
    LaurentNormalizedReduction.firstUnit_natural, RingHom.comp_apply] at he
  simpa only [← map_pow] using he

/-- The canonical top obstruction retains the second identity normalization. -/
theorem completeIdentityFiniteMulObstruction_secondUnit (hm : (δ m) = 0) :
    (ε K[T;T⁻¹]) (O) = 0 := by
  apply (laurent_top_lift_eq_zero_iff K (m + 1) _).mp
  have he := completeIdentityFiniteMulDefect_secondUnit K n h i (m + 1)
  rw [completeIdentityFiniteMulDefect_from_obstruction K n h i m hm,
    map_mul, map_pow] at he
  have hc : (ε (A (m + 1))[T;T⁻¹]) (C (C (parameter K (m + 1)))) =
      C (parameter K (m + 1)) := by
    change LaurentUnitPoints.evalUnit (R := (A (m + 1))[T;T⁻¹])
      (1 : (A (m + 1))[T;T⁻¹]ˣ) _ = _
    exact LaurentUnitPoints.evalUnit_C _ _
  rw [hc] at he
  rw [← RingHom.comp_apply,
    LaurentNormalizedReduction.secondUnit_natural, RingHom.comp_apply] at he
  simpa only [← map_pow] using he

end FLT.Mazur.PolygonInfinitesimalStages
