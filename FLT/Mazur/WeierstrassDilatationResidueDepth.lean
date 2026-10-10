/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSplitNodeDilatation

/-!
# Exact residue coefficients of the divided split nodal chart

Cancellation of uniformizer powers determines the actual reduced equation.
Before the middle depth its constant term vanishes; at the middle depth it
is a unit. Thus these two fibers must not be conflated in the resolution.
-/

@[expose] public section

open IsLocalRing

namespace FLT.Mazur.WeierstrassDilatation

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n : ℕ} (D : SplitNodeDepth W π n)

include D in
/-- Dividing by a uniformizer power subtracts that power from ideal depth. -/
theorem divided_mem_power {b : R} (k l : ℕ)
    (h : π ^ k * b ∈ maximalIdeal R ^ (k + l)) : b ∈ maximalIdeal R ^ l := by
  rw [D.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero k D.uniformizer_ne_zero)
  simpa only [pow_add, mul_assoc] using hc

include D in
/-- The linear divided coefficients vanish in the residue field at every bounded depth. -/
theorem divided_linear_mem (k : ℕ) (hk : 2 * k ≤ n) (b3 b4 : R)
    (h3 : W.a₃ = π ^ k * b3) (h4 : W.a₄ = π ^ k * b4) :
    b3 ∈ maximalIdeal R ∧ b4 ∈ maximalIdeal R := by
  have hm : maximalIdeal R ^ (n + 1) ≤ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_le_pow_right (by omega)
  constructor
  · simpa using divided_mem_power D k 1 (h3 ▸ hm D.a₃_mem)
  · simpa using divided_mem_power D k 1 (h4 ▸ hm D.a₄_mem)

include D in
/-- Strictly before the middle depth the divided constant still vanishes modulo the base. -/
theorem divided_constant_mem (k : ℕ) (hk : 2 * k < n) (b6 : R)
    (h6 : W.a₆ = (π ^ k) ^ 2 * b6) : b6 ∈ maximalIdeal R := by
  have h : π ^ (2 * k) * b6 ∈ maximalIdeal R ^ (2 * k + 1) := by
    have hm := Ideal.pow_le_pow_right (by omega : 2 * k + 1 ≤ n) D.a₆_mem
    simpa only [h6, ← pow_mul, Nat.mul_comm k 2] using hm
  simpa using divided_mem_power D (2 * k) 1 h

omit [IsDomain R] in
include D in
/-- At the exact middle depth the divided constant is a unit, rather than a node. -/
theorem divided_constant_isUnit (k : ℕ) (hk : 2 * k = n) (b6 : R)
    (h6 : W.a₆ = (π ^ k) ^ 2 * b6) : IsUnit b6 := by
  rw [← notMem_maximalIdeal]
  intro hb
  apply D.a₆_not_mem
  rw [h6, ← pow_mul, Nat.mul_comm k 2, hk]
  have hp : π ^ n ∈ maximalIdeal R ^ n := by
    rw [D.maximalIdeal_eq, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [pow_succ] using Ideal.mul_mem_mul hp hb

omit [IsDomain R] in
include D in
/-- The scale vanishes on the residue fiber at every positive depth. -/
theorem residue_scale_eq_zero (k : ℕ) (hk : 0 < k) : residue R (π ^ k) = 0 := by
  have hp : π ∈ maximalIdeal R := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  rw [map_pow, (residue_eq_zero_iff π).mpr hp, zero_pow (Nat.ne_of_gt hk)]

end FLT.Mazur.WeierstrassDilatation
