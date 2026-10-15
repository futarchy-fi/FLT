/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstLaurentPairProduct
public import FLT.Mazur.LaurentBoundaryTailShift

/-!
# Positive node powers clear arbitrary first-layer branch errors

Every parameter-annihilated pair becomes an original node function after
multiplication by a sufficiently high power of either node coordinate.
This is a conductor calculation in the full nonreduced branch algebra.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentBoundaryTailShift PolygonScalingNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "L" => (S)[T;T⁻¹]
local notation "β" => firstNodeBranchPair R
local notation "C" => firstNodeBranchSubalgebra R
local notation "x" => leftCoordinate (e)
local notation "y" => rightCoordinate (e)

/-- Reduction of the left node coordinate retains just its actual left Laurent coordinate. -/
theorem firstNodePairReduction_left :
    firstNodePairReduction R ((β) (x)) = (T 1, 0) := by
  have he : (reduction R 1).toRingHom (e) = 0 := reduction_parameter R 1
  change (coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) (x)),
    coeffMap (reduction R 1).toRingHom
      (leftLaurentMap (e) (branchSwapMap (e) (x)))) = _
  rw [leftLaurentMap_left, branchSwapMap_left, leftLaurentMap_right,
    map_mul, coeffMap_C, he, map_zero, zero_mul,
    LaurentCoefficientEvaluation.coeffMap_T]

/-- The opposite coordinate has the corresponding original right reduction. -/
theorem firstNodePairReduction_right :
    firstNodePairReduction R ((β) (y)) = (0, T 1) := by
  have he : (reduction R 1).toRingHom (e) = 0 := reduction_parameter R 1
  change (coeffMap (reduction R 1).toRingHom (leftLaurentMap (e) (y)),
    coeffMap (reduction R 1).toRingHom
      (leftLaurentMap (e) (branchSwapMap (e) (y)))) = _
  rw [leftLaurentMap_right, branchSwapMap_right, leftLaurentMap_left,
    map_mul, coeffMap_C, he, map_zero, zero_mul,
    LaurentCoefficientEvaluation.coeffMap_T]

/-- A positive left power kills the opposite branch of every weighted pair. -/
theorem firstNodeParameterPair_mul_left_pow (p : R[T;T⁻¹] × R[T;T⁻¹])
    (m : ℕ) (hm : 0 < m) :
    firstNodeParameterPair R p * (β) ((x) ^ m) =
      firstNodeParameterPair R (p.1 * T (m : ℤ), 0) := by
  rw [firstNodeParameterPair_mul, map_pow, map_pow, firstNodePairReduction_left]
  congr 1
  apply Prod.ext
  · change p.1 * (T 1) ^ m = _
    rw [T_pow, mul_one]
  · change p.2 * (0 : R[T;T⁻¹]) ^ m = 0
    rw [zero_pow (Nat.ne_of_gt hm), mul_zero]

/-- A positive right power kills the other branch and shifts the surviving coefficients. -/
theorem firstNodeParameterPair_mul_right_pow (p : R[T;T⁻¹] × R[T;T⁻¹])
    (m : ℕ) (hm : 0 < m) :
    firstNodeParameterPair R p * (β) ((y) ^ m) =
      firstNodeParameterPair R (0, p.2 * T (m : ℤ)) := by
  rw [firstNodeParameterPair_mul, map_pow, map_pow, firstNodePairReduction_right]
  congr 1
  apply Prod.ext
  · change p.1 * (0 : R[T;T⁻¹]) ^ m = 0
    rw [zero_pow (Nat.ne_of_gt hm), mul_zero]
  · change p.2 * (T 1) ^ m = _
    rw [T_pow, mul_one]

/-- Every weighted pair has a positive left conductor power into the full original node. -/
theorem firstNodeParameterPair_left_conductor (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    ∃ m : ℕ, 0 < m ∧ firstNodeParameterPair R p * (β) ((x) ^ m) ∈ (C) := by
  obtain ⟨m, hm, hp⟩ := exists_positive_shift p.1
  refine ⟨m, hm, ?_⟩
  rw [firstNodeParameterPair_mul_left_pow R p m hm]
  change (firstLaurentParameterLift R _, firstLaurentParameterLift R 0) ∈ (C)
  rw [firstLaurentParameterLift_zero, firstNodeBranchSubalgebra_parameter_left_iff, mul_comm]
  exact hp

/-- Every weighted pair also has a positive right conductor power. -/
theorem firstNodeParameterPair_right_conductor (p : R[T;T⁻¹] × R[T;T⁻¹]) :
    ∃ m : ℕ, 0 < m ∧ firstNodeParameterPair R p * (β) ((y) ^ m) ∈ (C) := by
  obtain ⟨m, hm, hp⟩ := exists_positive_shift p.2
  refine ⟨m, hm, ?_⟩
  rw [firstNodeParameterPair_mul_right_pow R p m hm]
  change (firstLaurentParameterLift R 0, firstLaurentParameterLift R _) ∈ (C)
  rw [firstLaurentParameterLift_zero, firstNodeBranchSubalgebra_parameter_right_iff, mul_comm]
  exact hp

/-- The left conductor exists for every full pair annihilated by the smoothing parameter. -/
theorem firstNodePair_annihilator_left_conductor (z : (L) × (L)) (hz : (e) • z = 0) :
    ∃ m : ℕ, 0 < m ∧ z * (β) ((x) ^ m) ∈ (C) := by
  rw [← firstNodePairCoefficient_reconstruct R z hz]
  exact firstNodeParameterPair_left_conductor R _

/-- The right conductor likewise retains arbitrary parameter-annihilated functions. -/
theorem firstNodePair_annihilator_right_conductor (z : (L) × (L)) (hz : (e) • z = 0) :
    ∃ m : ℕ, 0 < m ∧ z * (β) ((y) ^ m) ∈ (C) := by
  rw [← firstNodePairCoefficient_reconstruct R z hz]
  exact firstNodeParameterPair_right_conductor R _

end FLT.Mazur.PolygonInfinitesimalStages
