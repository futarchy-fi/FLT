/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstNodeParameterScaling
public import FLT.Mazur.PolygonFirstNodePolynomialDescent
public import FLT.Mazur.PolygonFirstNodeBranchAutomorphism

/-!
# Exact function-descent tests for the two original node coordinates

Subtract the original scaled node coordinate from a proposed branch pair.
Its opposite-branch difference is automatically zero, while its remaining
difference is the parameter-weighted Laurent error. Thus membership in the
actual node subalgebra is exactly a polynomial boundary condition.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial LaurentUnitPoints PolygonChartScaling
open PolygonScalingNaturality LaurentCoefficientEvaluation LaurentPositivePart
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable (R : Type) [CommRing R]
local notation "S" => Ring R 1
local notation "e" => parameter R 1
local notation "B" => ChartRing (e)
local notation "L" => (S)[T;T⁻¹]

/-- Scalar multiplication on a parameter-layer function uses the scalar's exact closed value. -/
theorem firstLaurentParameterLift_scalar (s : S) (p : R[T;T⁻¹]) :
    C s * firstLaurentParameterLift R p =
      firstLaurentParameterLift R (C (reduction R 1 s) * p) := by
  simp only [firstLaurentParameterLift, map_mul, coeffMap_C]
  rw [← mul_assoc, ← map_mul, mul_comm s (e), firstParameter_mul_reduction,
    map_mul, mul_assoc]

/-- A unit with closed coordinate aT has exactly the scaled inverse on the parameter ideal. -/
theorem firstLaurent_parameter_inverse_scaling (v : (L)ˣ) (a : (S)ˣ)
    (hv : coeffMap (reduction R 1).toRingHom v.val = C (reduction R 1 a.val) * T 1) :
    C (e) * v⁻¹.val = C (e) * (coordinateUnit a)⁻¹.val := by
  have he : coeffMap (reduction R 1).toRingHom v.val =
      coeffMap (reduction R 1).toRingHom (coordinateUnit a).val := by
    apply hv.trans
    change _ = coeffMap (reduction R 1).toRingHom (C a.val * T 1)
    rw [map_mul, coeffMap_C, coeffMap_T]
    rfl
  simpa only [evalUnit_T, zpow_neg_one] using
    firstLaurent_evalUnit_parameter_eq R v (coordinateUnit a) he (T (-1))

/-- The exact full difference of the proposed first coordinate and its original node scaling. -/
theorem firstNodeBranchLeftImage_difference (u v : (L)ˣ) (a : (S)ˣ) (p : R[T;T⁻¹])
    (hu : u.val = C a.val * T 1 + firstLaurentParameterLift R p)
    (hv : coeffMap (reduction R 1).toRingHom v.val = C (reduction R 1 a⁻¹.val) * T 1) :
    firstNodeBranchLeftImage R u v -
        firstNodeBranchPair R (reciprocalScale (e) a (leftCoordinate (e))) =
      (firstLaurentParameterLift R p, 0) := by
  rw [← firstNodeBranchPair_scaling, firstNodeBranchSubstitution_left]
  apply Prod.ext
  · change u.val - (coordinateUnit a).val = firstLaurentParameterLift R p
    rw [hu]
    change C a.val * T 1 + firstLaurentParameterLift R p - C a.val * T 1 = _
    abel
  · change C (e) * v⁻¹.val - C (e) * (coordinateUnit a⁻¹)⁻¹.val = 0
    rw [firstLaurent_parameter_inverse_scaling R v a⁻¹ hv, sub_self]

/-- Membership of the first actual coordinate pair is equivalent to vanishing of its error tail. -/
theorem firstNodeBranchLeftImage_mem_iff (u v : (L)ˣ) (a : (S)ˣ) (p : R[T;T⁻¹])
    (hu : u.val = C a.val * T 1 + firstLaurentParameterLift R p)
    (hv : coeffMap (reduction R 1).toRingHom v.val = C (reduction R 1 a⁻¹.val) * T 1) :
    firstNodeBranchLeftImage R u v ∈ firstNodeBranchSubalgebra R ↔ boundaryTail p = 0 := by
  have hs : firstNodeBranchPair R (reciprocalScale (e) a (leftCoordinate (e))) ∈
      firstNodeBranchSubalgebra R := ⟨_, rfl⟩
  rw [← firstNodeBranchSubalgebra_parameter_left_iff,
    ← firstNodeBranchLeftImage_difference R u v a p hu hv]
  constructor
  · intro hm
    exact (firstNodeBranchSubalgebra R).sub_mem hm hs
  · intro hm
    simpa only [sub_add_cancel] using (firstNodeBranchSubalgebra R).add_mem hm hs

/-- Swapping the original branches gives the full second-coordinate test, without a map witness. -/
theorem firstNodeBranchRightImage_mem_iff (u v : (L)ˣ) (a : (S)ˣ) (q : R[T;T⁻¹])
    (hu : coeffMap (reduction R 1).toRingHom u.val = C (reduction R 1 a.val) * T 1)
    (hv : v.val = C a⁻¹.val * T 1 + firstLaurentParameterLift R q) :
    firstNodeBranchRightImage R u v ∈ firstNodeBranchSubalgebra R ↔ boundaryTail q = 0 := by
  have hu' : coeffMap (reduction R 1).toRingHom u.val =
      C (reduction R 1 (a⁻¹)⁻¹.val) * T 1 := by simpa only [inv_inv] using hu
  rw [← firstNodeBranchLeftImage_mem_iff R v u a⁻¹ q hv hu']
  constructor
  · exact firstNodeBranchLeftImage_swap R u v
  · intro hm
    exact firstNodeBranchRightImage_swap R v u hm

end FLT.Mazur.PolygonInfinitesimalStages
