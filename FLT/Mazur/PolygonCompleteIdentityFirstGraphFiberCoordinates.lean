/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFiberSupport
public import FLT.Mazur.PolygonSmoothingSumRegular

/-!
# Original node coordinates on the literal graph special fiber

The original source coordinates satisfy xy=0 in the actual special fiber.
Their sum reduces to the regular original node parameter. Consequently
every function killed by this sum lies in the residual square-zero kernel.
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
local notation "Q" => completeIdentityFirstGraphSpecialFiber K n h i
local notation "q" => completeIdentityFirstGraphFiberQuotient K n h i
local notation "s" => completeIdentityFirstGraphSource K n h i
local notation "f" => completeIdentityFirstGraphFiberReduction K n h i
/-- Cache the existing graph ring for the original coordinate calculations. -/
local instance completeIdentityFirstGraphFiberCoordinatesCommRing : CommRing (E) := inferInstance

/-- The unchanged source left coordinate in the literal special fiber. -/
def completeIdentityFirstGraphFiberLeft : Q := (q) ((s) (leftCoordinate (e)))

/-- The unchanged source right coordinate in the literal special fiber. -/
def completeIdentityFirstGraphFiberRight : Q := (q) ((s) (rightCoordinate (e)))

local notation "x" => completeIdentityFirstGraphFiberLeft K n h i
local notation "y" => completeIdentityFirstGraphFiberRight K n h i

/-- Reduction retains the original left coordinate. -/
theorem completeIdentityFirstGraphFiberLeft_reduction :
    (f) (x) = leftCoordinate (0 : R) := by
  rw [completeIdentityFirstGraphFiberLeft, completeIdentityFirstGraphFiberReduction_mk,
    completeIdentityFirstGraphReduction_source, firstNodeReduction_left]

/-- Reduction retains the original right coordinate. -/
theorem completeIdentityFirstGraphFiberRight_reduction :
    (f) (y) = rightCoordinate (0 : R) := by
  rw [completeIdentityFirstGraphFiberRight, completeIdentityFirstGraphFiberReduction_mk,
    completeIdentityFirstGraphReduction_source, firstNodeReduction_right]

/-- Both coordinates are exactly the images under the original-source section. -/
theorem completeIdentityFirstGraphFiberCoordinates_section :
    completeIdentityFirstGraphFiberSection K n h i (leftCoordinate (0 : R)) = (x) ∧
      completeIdentityFirstGraphFiberSection K n h i (rightCoordinate (0 : R)) = (y) := by
  constructor
  · rw [← firstNodeReduction_left (R), completeIdentityFirstGraphFiberSection_reduction]
    rfl
  · rw [← firstNodeReduction_right (R), completeIdentityFirstGraphFiberSection_reduction]
    rfl

/-- The literal special fiber satisfies the original reduced node equation. -/
theorem completeIdentityFirstGraphFiberCoordinates_mul : (x) * (y) = 0 := by
  obtain ⟨hx, hy⟩ := completeIdentityFirstGraphFiberCoordinates_section K n h i
  rw [← hx, ← hy, ← map_mul, coordinate_relation, map_zero, map_zero]

/-- Any function killed by the original coordinate sum belongs to the residual kernel. -/
theorem completeIdentityFirstGraphFiber_sum_kernel (z : Q) (hz : ((x) + (y)) * z = 0) :
    (f) z = 0 := by
  have he := congrArg (f) hz
  rw [map_mul, map_add, completeIdentityFirstGraphFiberLeft_reduction,
    completeIdentityFirstGraphFiberRight_reduction, map_zero] at he
  exact (branchSum_regular (0 : R)).left (he.trans (mul_zero _).symm)

end FLT.Mazur.PolygonInfinitesimalStages
