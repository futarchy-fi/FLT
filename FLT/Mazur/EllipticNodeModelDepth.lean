/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeGenericNonsingular

/-!
# The depth of a split model is intrinsic under integral changes

The exact a₆ depth in a split depth model is also the exact discriminant
depth. Integral unit variable changes preserve it, so different normalized
models can always be compared at the same label modulus.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π π' : R} {n m : ℕ}

/-- The depth recorded by a split model is exactly its discriminant depth. -/
theorem SplitNodeDepth.discriminant_exact_depth (D : SplitNodeDepth W π n) :
    W.Δ ∈ maximalIdeal R ^ n ∧ W.Δ ∉ maximalIdeal R ^ (n + 1) := by
  have h6 := Ideal.pow_le_self (Nat.ne_of_gt D.depth_pos) D.a₆_mem
  exact ⟨(node_discriminant_mem_pow_iff W D.a₁_unit D.a₂_mem h6 n
    (Ideal.pow_le_pow_right (by omega) D.a₃_mem)
    (Ideal.pow_le_pow_right (by omega) D.a₄_mem)).mpr D.a₆_mem,
    fun h => D.a₆_not_mem
      ((node_discriminant_mem_pow_iff W D.a₁_unit D.a₂_mem h6 (n + 1)
        D.a₃_mem D.a₄_mem).mp h)⟩

/-- Two split depth models related by an integral unit change have the same depth. -/
theorem splitNodeDepth_variableChange_depth_eq (D : SplitNodeDepth W π n)
    (C : VariableChange R) (D' : SplitNodeDepth (C • W) π' m) : n = m := by
  obtain ⟨hd, hd'⟩ := D.discriminant_exact_depth
  obtain ⟨he, he'⟩ := D'.discriminant_exact_depth
  have hmem (k : ℕ) : (C • W).Δ ∈ maximalIdeal R ^ k ↔ W.Δ ∈ maximalIdeal R ^ k := by
    rw [variableChange_Δ]
    exact (maximalIdeal R ^ k).unit_mul_mem_iff_mem (C.u⁻¹.isUnit.pow 12)
  rw [hmem] at he he'
  apply Nat.le_antisymm
  · by_contra h
    exact he' (Ideal.pow_le_pow_right (by omega : m + 1 ≤ n) hd)
  · by_contra h
    exact hd' (Ideal.pow_le_pow_right (by omega : n + 1 ≤ m) he)

end FLT.Mazur
