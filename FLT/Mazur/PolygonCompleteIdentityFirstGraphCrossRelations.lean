/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberGenerators
public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberCoordinates
public import FLT.Mazur.PolygonCompleteIdentityFirstPrincipalCoordinates
public import FLT.Mazur.PolygonFirstNodeWeightedConductor

/-!
# Exact cross-coordinate annihilators of the original graph errors

Each original coordinate error is killed by the opposite original coordinate
already in the full graph ring. These identities descend to the literal
special fiber and refine the support of its two actual kernel generators.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstErrorAlgebra
  completeIdentityFirstGraphReduction completeIdentityFirstGraphSource
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "e" => parameter (R) 1
local notation "E" => completeIdentityFirstErrorAlgebra K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "D" => completeIdentityFirstGraphError K n h i
local notation "q" => completeIdentityFirstGraphFiberQuotient K n h i
local notation "x" => leftCoordinate (e)
local notation "y" => rightCoordinate (e)
/-- Cache the original graph ring for the cross-coordinate identities. -/
local instance completeIdentityFirstGraphCrossRelationsCommRing : CommRing (E) := inferInstance

/-- The first original graph error is killed by the original opposite coordinate. -/
theorem completeIdentityFirstGraphError_left_mul_right : (D) (x) * (s) (y) = 0 := by
  apply Subtype.ext
  change ((D) (x)).val * ((s) (y)).val = 0
  rw [completeIdentityFirstGraphError_val, completeIdentityFirstGraphSource_apply,
    ← completeIdentityFirstReducedDefect_reduction, firstNodeReduction_left,
    completeIdentityFirstReducedDefect_left]
  have he := firstNodeParameterPair_mul_right_pow (R)
    (completeIdentityFiniteMulObstruction K n h i 0, 0) 1 (by decide)
  simpa only [pow_one, zero_mul, Prod.mk_zero_zero, map_zero] using he

/-- The second original graph error is killed by the other original coordinate. -/
theorem completeIdentityFirstGraphError_right_mul_left : (D) (y) * (s) (x) = 0 := by
  apply Subtype.ext
  change ((D) (y)).val * ((s) (x)).val = 0
  rw [completeIdentityFirstGraphError_val, completeIdentityFirstGraphSource_apply,
    ← completeIdentityFirstReducedDefect_reduction, firstNodeReduction_right,
    completeIdentityFirstReducedDefect_right]
  have he := firstNodeParameterPair_mul_left_pow (R)
    (0, completeIdentityFirstReciprocalError K n h i) 1 (by decide)
  simpa only [pow_one, zero_mul, Prod.mk_zero_zero, map_zero] using he

/-- The first actual residual generator is killed by the unchanged right fiber coordinate. -/
theorem completeIdentityFirstGraphFiberError_left_mul_right :
    completeIdentityFirstGraphFiberError K n h i (x) *
      completeIdentityFirstGraphFiberRight K n h i = 0 := by
  change (q) ((D) (x)) * (q) ((s) (y)) = 0
  rw [← (q).map_mul, completeIdentityFirstGraphError_left_mul_right, (q).map_zero]

/-- The second actual residual generator is killed by the unchanged left fiber coordinate. -/
theorem completeIdentityFirstGraphFiberError_right_mul_left :
    completeIdentityFirstGraphFiberError K n h i (y) *
      completeIdentityFirstGraphFiberLeft K n h i = 0 := by
  change (q) ((D) (y)) * (q) ((s) (x)) = 0
  rw [← (q).map_mul, completeIdentityFirstGraphError_right_mul_left, (q).map_zero]

end FLT.Mazur.PolygonInfinitesimalStages
