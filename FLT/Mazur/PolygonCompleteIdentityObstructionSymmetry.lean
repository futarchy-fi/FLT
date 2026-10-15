/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFiniteSymmetry
public import FLT.Mazur.PolygonCompleteIdentityMixedObstruction
public import FLT.Mazur.PolygonLaurentTopLiftRecovery

/-!
# Symmetry of the original reduced and mixed obstructions

The original finite multiplication symmetry descends through the injective top
layer. Removing the two identity factors preserves this proven symmetry.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial PolygonScalingNaturality LaurentPairSwap
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "A" => Ring K (m + 1)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "M" => completeIdentityMixedObstruction K n h i m
local notation "D" => (C (T 1 - 1) * (T 1 - 1) : K[T;T⁻¹][T;T⁻¹])

/-- Original commutativity descends to the actual next-order reduced obstruction. -/
theorem completeIdentityFiniteMulObstruction_swap
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) : swap K (O) = (O) := by
  apply doubleLaurent_top_lift_injective K (m + 1)
  have he := congrArg (swap (A))
    (completeIdentityFiniteMulDefect_from_obstruction K n h i m hm)
  rw [completeIdentityFiniteMulDefect_swap, map_mul, map_pow, swap_C, coeffMap_C] at he
  have hn := congrArg (fun f : K[T;T⁻¹][T;T⁻¹] →+* (A)[T;T⁻¹][T;T⁻¹] ↦ f (O))
    (swap_natural K (algebraMap K (A)))
  change swap (A) (coeffMap (coeffMap (algebraMap K (A))) (O)) =
    coeffMap (coeffMap (algebraMap K (A))) (swap K (O)) at hn
  rw [hn] at he
  exact he.symm.trans (completeIdentityFiniteMulDefect_from_obstruction K n h i m hm)

/-- Input exchange preserves the exact product of identity equations. -/
theorem completeIdentityMixedFactor_swap : swap K (D) = (D) := by
  rw [map_mul, swap_C, map_sub, coeffMap_T_one, map_one,
    map_sub, swap_T_one, map_one, map_sub, map_one]
  exact mul_comm _ _

/-- The uniquely determined mixed obstruction inherits the actual original symmetry. -/
theorem completeIdentityMixedObstruction_swap
    (hm : completeIdentityFiniteMulDefect K n h i m = 0) : swap K (M) = (M) := by
  apply completeIdentityMixedObstruction_unique K n h i m hm
  have he := congrArg (swap K) (completeIdentityMixedObstruction_factor K n h i m hm)
  rw [completeIdentityFiniteMulObstruction_swap K n h i m hm,
    map_mul, completeIdentityMixedFactor_swap] at he
  exact he

/-- Symmetry at the first positive order requires no unproved lower-order law. -/
theorem completeIdentityMixedObstruction_zero_swap :
    swap K (completeIdentityMixedObstruction K n h i 0) =
      completeIdentityMixedObstruction K n h i 0 :=
  completeIdentityMixedObstruction_swap K n h i 0 (completeIdentityFiniteMulDefect_zero K n h i)

end FLT.Mazur.PolygonInfinitesimalStages
