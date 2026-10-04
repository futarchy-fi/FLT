/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Module.Pi

/-! # Torsion in a free module over a principal-power quotient -/

@[expose] public noncomputable section
namespace Ideal.Quotient
variable {R : Type*} [CommRing R] [IsDomain R] (a : R) (ha : a ≠ 0) (n : ℕ)

include ha in
/-- In R/(a^(n+1)), every element killed by a is a multiple of a^n. -/
theorem exists_pow_mul_of_mul_eq_zero
    (x : R ⧸ Ideal.span {a ^ (n + 1)}) (hx : algebraMap R _ a * x = 0) :
    ∃ y : R ⧸ Ideal.span {a ^ (n + 1)}, algebraMap R _ (a ^ n) * y = x := by
  obtain ⟨b, rfl⟩ := mk_surjective x
  have hb : a * b ∈ Ideal.span {a ^ (n + 1)} := by
    apply eq_zero_iff_mem.mp
    simpa only [map_mul, Ideal.Quotient.algebraMap_eq] using hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
  have he : a ^ n * c = b := by
    apply mul_left_cancel₀ ha
    rw [← mul_assoc, ← pow_succ']
    exact hc.symm
  refine ⟨mk _ c, ?_⟩
  change mk _ (a ^ n) * mk _ c = _
  rw [← map_mul, he]

include ha in
/-- Coordinatewise cancellation gives the same divisibility in every free function module. -/
theorem exists_pow_smul_of_smul_eq_zero {ι : Type*}
    (x : ι → R ⧸ Ideal.span {a ^ (n + 1)}) (hx : a • x = 0) :
    ∃ y : ι → R ⧸ Ideal.span {a ^ (n + 1)}, a ^ n • y = x := by
  have h (i : ι) : algebraMap R _ a * x i = 0 := congrFun hx i
  choose y hy using fun i ↦ exists_pow_mul_of_mul_eq_zero a ha n (x i) (h i)
  exact ⟨y, funext hy⟩

end Ideal.Quotient
