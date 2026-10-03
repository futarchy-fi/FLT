/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolynomialEndpointInterpolation
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Weighted matching of bounded polynomial families

The discrepancy map has a right inverse, and matching families realize arbitrary
node values. Their dimension is the sum of the positive component degrees.
The neighbor function and weights are explicit inputs; no sheaf comparison or
ampleness assertion is made. For the polygon pinching convention, the neighbor
is the predecessor, since zero on i is identified with infinity on next(i).
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.PolygonPolynomialMatching
open PolynomialEndpointInterpolation
variable {R ι : Type*} [CommRing R]
variable (d : ι → ℕ) (neighbor : ι → ι) (weight : ι → R)

/-- Weighted endpoint discrepancy of a bounded polynomial family. -/
def difference : (∀ i, Bounded R (d i)) →ₗ[R] (ι → R) where
  toFun p i := (endpoints (d i) (p i)).2 -
    weight i * (endpoints (d (neighbor i)) (p (neighbor i))).1
  map_add' p q := by ext i; simp [map_add, mul_add]; ring
  map_smul' a p := by ext i; simp [map_smul]; ring

/-- The kernel of the explicit polynomial discrepancy map. -/
abbrev matching := LinearMap.ker (difference d neighbor weight)

/-- Kernel membership is precisely the weighted coefficient relation. -/
theorem mem_matching (p : ∀ i, Bounded R (d i)) :
    p ∈ matching d neighbor weight ↔ ∀ i,
      (p i).val.coeff (d i + 1) = weight i * (p (neighbor i)).val.coeff 0 := by
  simp [matching, LinearMap.mem_ker, difference, endpoints, funext_iff, sub_eq_zero]

/-- A discrepancy lift with zero constant coefficients on every component. -/
def correction : (ι → R) →ₗ[R] (∀ i, Bounded R (d i)) where
  toFun v i := interpolate (d i) (0, v i)
  map_add' v w := by
    ext i : 1
    simpa using (interpolate (R := R) (d i)).map_add (0, v i) (0, w i)
  map_smul' a v := by
    ext i : 1
    simpa using (interpolate (R := R) (d i)).map_smul a (0, v i)

/-- The correction is a right inverse to discrepancy. -/
@[simp] theorem difference_correction (v : ι → R) :
    difference d neighbor weight (correction d v) = v := by
  ext i
  simp [difference, correction]

/-- Every discrepancy vector has a polynomial lift. -/
theorem difference_surjective : Function.Surjective (difference d neighbor weight) :=
  fun v ↦ ⟨correction d v, difference_correction d neighbor weight v⟩

/-- Interpolate a matching polynomial family from arbitrary node values. -/
def nodeLift (v : ι → R) : matching d neighbor weight :=
  ⟨fun i ↦ interpolate (d i) (v i, weight i * v (neighbor i)), by
    change difference d neighbor weight _ = 0
    ext i
    simp [difference]⟩

/-- The node lift has the prescribed constant coefficients. -/
@[simp] theorem nodeLift_constant (v : ι → R) (i : ι) :
    ((nodeLift d neighbor weight v).val i).val.coeff 0 = v i := by
  change (endpoints (d i) (interpolate (d i) _)).1 = _
  rw [endpoints_interpolate]

/-- Matching polynomial families realize arbitrary node values. -/
theorem nodeValues_surjective : Function.Surjective
    (fun p : matching d neighbor weight ↦ fun i ↦ (p.val i).val.coeff 0) :=
  fun v ↦ ⟨nodeLift d neighbor weight v, funext (nodeLift_constant d neighbor weight v)⟩

/-- Subtracting the explicit discrepancy lift produces a matching family. -/
theorem corrected_mem (p : ∀ i, Bounded R (d i)) :
    p - correction d (difference d neighbor weight p) ∈ matching d neighbor weight := by
  rw [LinearMap.mem_ker, map_sub, difference_correction, sub_self]

variable (K : Type*) [Field K] [Fintype ι]

/-- Matching families have dimension equal to the sum of component degrees. -/
theorem finrank_matching (w : ι → K) :
    Module.finrank K (matching d neighbor w) = ∑ i, (d i + 1) := by
  have h := (difference d neighbor w).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (difference_surjective d neighbor w),
    finrank_top, Module.finrank_pi, Module.finrank_pi_fintype] at h
  simp only [finrank_bounded] at h
  have hs : (∑ i, (d i + 2)) = (∑ i, (d i + 1)) + Fintype.card ι := by
    simp only [show ∀ i, d i + 2 = (d i + 1) + 1 from fun _ ↦ by omega,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  change Module.finrank K (LinearMap.ker (difference d neighbor w)) = _
  omega
end FLT.Mazur.PolygonPolynomialMatching
