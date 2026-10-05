/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Ideal.Operations

/-!+# Increasing the depth of nodal coefficients

When a₁ is a unit and a₂ lies in I, an integral translation moves a₃,a₄
from Iᵏ to Iᵏ⁺¹. The translation lies in Iᵏ and changes a₆ only in I²ᵏ.
No division by 2 or 3 is needed, so this step applies in every residue
characteristic. Iteration is a separate finite normalization argument.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- One translation kills a₃ exactly and increases the depth of a₄. -/
theorem exists_node_depth_step (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ I)
    {k : ℕ} (hk : 1 ≤ k) (h3 : W.a₃ ∈ I ^ k) (h4 : W.a₄ ∈ I ^ k) :
    ∃ r t : R, r ∈ I ^ k ∧ t ∈ I ^ k ∧
      let V := VariableChange.mk 1 r 0 t • W
      V.a₁ = W.a₁ ∧ V.a₂ ∈ I ∧ V.a₃ = 0 ∧ V.a₄ ∈ I ^ (k + 1) ∧
        V.a₆ - W.a₆ ∈ I ^ (2 * k) := by
  obtain ⟨u, hu⟩ := h1
  let t : R := ↑u⁻¹ * W.a₄
  let r : R := -(↑u⁻¹ * (W.a₃ + 2 * t))
  have ht : t ∈ I ^ k := (I ^ k).mul_mem_left _ h4
  have hr : r ∈ I ^ k := (I ^ k).neg_mem
    ((I ^ k).mul_mem_left _ ((I ^ k).add_mem h3 ((I ^ k).mul_mem_left _ ht)))
  have hrI : r ∈ I := Ideal.pow_le_self (by omega) hr
  have ht1 : t * W.a₁ = W.a₄ := by
    rw [← hu]
    dsimp [t]
    rw [mul_comm (↑u⁻¹ * W.a₄), ← mul_assoc, Units.mul_inv, one_mul]
  have hr1 : r * W.a₁ = -(W.a₃ + 2 * t) := by
    rw [← hu]
    dsimp only [r]
    rw [neg_mul, mul_comm (↑u⁻¹ * (W.a₃ + 2 * t)) (↑u), ← mul_assoc, Units.mul_inv, one_mul]
  have hr2 : r ^ 2 ∈ I ^ (2 * k) := by
    simpa only [pow_two, two_mul, pow_add] using Ideal.mul_mem_mul hr hr
  have hr2' : r ^ 2 ∈ I ^ (k + 1) :=
    Ideal.pow_le_pow_right (by omega) hr2
  have hrA2 : r * W.a₂ ∈ I ^ (k + 1) := by
    simpa only [pow_succ] using Ideal.mul_mem_mul hr h2
  have hrt : r * t ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul hr ht
  have hrA4 : r * W.a₄ ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul hr h4
  have htA3 : t * W.a₃ ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul ht h3
  have ht2 : t ^ 2 ∈ I ^ (2 * k) := by
    simpa only [pow_two, two_mul, pow_add] using Ideal.mul_mem_mul ht ht
  refine ⟨r, t, hr, ht, ?_⟩
  dsimp only
  have ha3 : (VariableChange.mk 1 r 0 t • W).a₃ = 0 := by
    simp [variableChange_def, hr1]
  have ha4 : (VariableChange.mk 1 r 0 t • W).a₄ =
      2 * (r * W.a₂) + 3 * r ^ 2 := by
    simp [variableChange_def, ht1]
    ring
  have ha6 : (VariableChange.mk 1 r 0 t • W).a₆ - W.a₆ =
      r * W.a₄ + W.a₂ * r ^ 2 + r * r ^ 2 - t * W.a₃ - t ^ 2 - W.a₁ * (r * t) := by
    simp only [variableChange_def]
    simp
    ring
  refine ⟨by simp [variableChange_def], ?_, ha3, ?_, ?_⟩
  · simpa [variableChange_def] using I.add_mem h2 (I.mul_mem_left 3 hrI)
  · rw [ha4]
    exact (I ^ (k + 1)).add_mem ((I ^ (k + 1)).mul_mem_left _ hrA2)
      ((I ^ (k + 1)).mul_mem_left _ hr2')
  · rw [ha6]
    exact (I ^ (2 * k)).sub_mem ((I ^ (2 * k)).sub_mem
      ((I ^ (2 * k)).sub_mem ((I ^ (2 * k)).add_mem
        ((I ^ (2 * k)).add_mem hrA4 ((I ^ (2 * k)).mul_mem_left _ hr2))
        ((I ^ (2 * k)).mul_mem_left _ hr2)) htA3) ht2)
      ((I ^ (2 * k)).mul_mem_left _ hrt)

end FLT.Mazur
