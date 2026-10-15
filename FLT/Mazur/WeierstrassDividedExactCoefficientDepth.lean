/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Exact depths of the original divided coefficients

The original split-node coefficient conditions and the actual division data
force deeper linear divisibility and exact constant depth before the middle stage.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n k : ℕ}
  (D : SplitNodeDepth W π n) (d : Data W π k)

include D in
/-- The divided linear coefficients keep all of their original excess depth. -/
theorem divided_linear_deep_mem (hk : k ≤ n + 1) :
    d.b3 ∈ maximalIdeal R ^ (n + 1 - k) ∧ d.b4 ∈ maximalIdeal R ^ (n + 1 - k) := by
  have he : k + (n + 1 - k) = n + 1 := by omega
  constructor
  · apply WeierstrassDilatation.divided_mem_power D k (n + 1 - k)
    rw [he, ← d.factor3]
    exact D.a₃_mem
  · apply WeierstrassDilatation.divided_mem_power D k (n + 1 - k)
    rw [he, ← d.factor4]
    exact D.a₄_mem

include D in
/-- Dividing the original constant subtracts exactly twice the horizontal depth. -/
theorem divided_constant_exact_depth (hk : 2 * k ≤ n) :
    d.b6 ∈ maximalIdeal R ^ (n - 2 * k) ∧ d.b6 ∉ maximalIdeal R ^ (n - 2 * k + 1) := by
  have he : 2 * k + (n - 2 * k) = n := by omega
  have hf : W.a₆ = π ^ (2 * k) * d.b6 := by
    simpa only [← pow_mul, Nat.mul_comm k 2] using d.factor6
  constructor
  · apply WeierstrassDilatation.divided_mem_power D (2 * k) (n - 2 * k)
    rw [he, ← hf]
    exact D.a₆_mem
  · intro hb
    apply D.a₆_not_mem
    rw [hf]
    have hp : π ^ (2 * k) ∈ maximalIdeal R ^ (2 * k) :=
      Ideal.pow_mem_pow (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π) (2 * k)
    have h := Ideal.mul_mem_mul hp hb
    rw [← pow_add, show 2 * k + (n - 2 * k + 1) = n + 1 by omega] at h
    exact h

end FLT.Mazur.WeierstrassDividedDepth
