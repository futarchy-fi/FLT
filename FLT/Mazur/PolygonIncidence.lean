/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicPinchingRotation
public import Mathlib.LinearAlgebra.Pi

/-!
# The cyclic incidence sequence

The kernel of cyclic difference consists of constants, and its image consists
of vectors with sum zero. A primitive is given by negative partialSum sums, so
no division by the number of components is needed. This includes one component
and positive characteristic dividing the number of components. No comparison
with scheme cohomology is asserted here.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace FLT.Mazur.PolygonIncidence

open PolygonPinching

variable (K : Type*) [Field K]

/-- Constant functions on the components. -/
def constant (n : ℕ) : K →ₗ[K] (Fin n → K) where
  toFun a _ := a
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Difference across each oriented edge of the cycle. -/
def difference {n : ℕ} (hn : 0 < n) : (Fin n → K) →ₗ[K] (Fin n → K) where
  toFun v i := v i - v (next hn i)
  map_add' v w := by ext i; simp; abel
  map_smul' a v := by ext i; simp [mul_sub]

/-- Sum of all node values. -/
def total (n : ℕ) : (Fin n → K) →ₗ[K] K where
  toFun v := ∑ i, v i
  map_add' v w := Finset.sum_add_distrib
  map_smul' a v := by simp [Finset.mul_sum]

@[simp]
theorem constant_apply (n : ℕ) (a : K) (i : Fin n) : constant K n a i = a := rfl

@[simp]
theorem difference_apply {n : ℕ} (hn : 0 < n) (v : Fin n → K) (i : Fin n) :
    difference K hn v i = v i - v (next hn i) := rfl

@[simp]
theorem total_apply (n : ℕ) (v : Fin n → K) : total K n v = ∑ i, v i := rfl

variable {K} {n : ℕ} (hn : 0 < n)

/-- Along a non-wrapping edge, successor is the ordinary natural successor. -/
theorem next_of_lt (i : Fin n) (hi : i.val + 1 < n) :
    next hn i = ⟨i.val + 1, hi⟩ := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt hi

/-- A function with zero cyclic difference takes its initial value everywhere. -/
theorem eq_initial_of_difference_eq_zero (v : Fin n → K)
    (hv : difference K hn v = 0) (i : Fin n) : v i = v ⟨0, hn⟩ := by
  have edge (j : Fin n) : v j = v (next hn j) :=
    sub_eq_zero.mp (congr_fun hv j)
  obtain ⟨i, hi⟩ := i
  induction i with
  | zero => rfl
  | succ i ih =>
    have hi' : i < n := by omega
    have hs := edge ⟨i, hi'⟩
    rw [next_of_lt hn _ hi] at hs
    exact hs.symm.trans (ih hi')

variable (K)

/-- Exactness at component constants. -/
theorem ker_difference :
    LinearMap.ker (difference K hn) = LinearMap.range (constant K n) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hv
    refine ⟨v ⟨0, hn⟩, ?_⟩
    funext i
    exact (eq_initial_of_difference_eq_zero hn v hv i).symm
  · rintro ⟨a, rfl⟩
    ext i
    simp

/-- Summing cyclic differences gives zero, since successor permutes the indices. -/
theorem total_difference (v : Fin n → K) : total K n (difference K hn v) = 0 := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  simp only [total_apply, difference_apply, Finset.sum_sub_distrib, sub_eq_zero,
    next_eq_add_one]
  exact (Equiv.sum_comp (Equiv.addRight (1 : Fin n)) v).symm

/-- Partial sums of a vector, extended periodically to natural-number indices. -/
def partialSum (v : Fin n → K) (m : ℕ) : K :=
  ∑ j ∈ Finset.range m, v ⟨j % n, Nat.mod_lt _ hn⟩

@[simp]
theorem partial_zero (v : Fin n → K) : partialSum K hn v 0 = 0 := by simp [partialSum]

theorem partial_succ (v : Fin n → K) (m : ℕ) :
    partialSum K hn v (m + 1) = partialSum K hn v m + v ⟨m % n, Nat.mod_lt _ hn⟩ :=
  Finset.sum_range_succ _ _

theorem partial_full (v : Fin n → K) : partialSum K hn v n = total K n v := by
  rw [partialSum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact Fin.ext (Nat.mod_eq_of_lt i.isLt)

/-- The explicit primitive for a vector of total zero. -/
def primitive (v : Fin n → K) (i : Fin n) : K := -partialSum K hn v i.val

/-- Negative partialSum sums invert cyclic difference on vectors of total zero. -/
theorem difference_primitive (v : Fin n → K) (hv : total K n v = 0) :
    difference K hn (primitive K hn v) = v := by
  funext i
  change -partialSum K hn v i.val - -partialSum K hn v (next hn i).val = v i
  have hs := partial_succ K hn v i.val
  have hm : (⟨i.val % n, Nat.mod_lt _ hn⟩ : Fin n) = i := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt i.isLt
  rw [hm] at hs
  by_cases hi : i.val + 1 < n
  · rw [next_of_lt hn i hi]
    dsimp
    rw [hs]
    abel
  · have hi' : i.val + 1 = n := by omega
    have hnext : (next hn i).val = 0 := by simp [next, hi']
    rw [hnext, partial_zero]
    rw [hi', partial_full, hv] at hs
    linear_combination hs

/-- Exactness at node values, uniformly in the characteristic. -/
theorem range_difference :
    LinearMap.range (difference K hn) = LinearMap.ker (total K n) := by
  ext v
  simp only [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨w, rfl⟩
    exact total_difference K hn w
  · intro hv
    exact ⟨primitive K hn v, difference_primitive K hn v hv⟩

include hn in
theorem total_surjective : Function.Surjective (total K n) := by
  classical
  intro a
  refine ⟨Pi.single ⟨0, hn⟩ a, ?_⟩
  simp

end FLT.Mazur.PolygonIncidence
