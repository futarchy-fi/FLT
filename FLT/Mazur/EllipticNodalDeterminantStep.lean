/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Increasing coefficient depth using the nodal determinant

Invertibility of b₂ solves both linear translation equations, without a
rational tangent direction or division by 2. The correction kills a₃,
leaves a₄ equal to 3r², and changes a₆ only at twice the starting depth.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- An invertible nodal determinant gives a depth-improving integral translation. -/
theorem exists_nodal_determinant_depth_step (hb : IsUnit W.b₂)
    {k : ℕ} (hk : 1 ≤ k) (h3 : W.a₃ ∈ I ^ k) (h4 : W.a₄ ∈ I ^ k) :
    ∃ r t : R, r ∈ I ^ k ∧ t ∈ I ^ k ∧
      let V := VariableChange.mk 1 r 0 t • W
      V.a₁ = W.a₁ ∧ V.b₂ - W.b₂ ∈ I ^ k ∧ V.a₃ = 0 ∧
        V.a₄ ∈ I ^ (k + 1) ∧ V.a₆ - W.a₆ ∈ I ^ (2 * k) := by
  obtain ⟨u, hu⟩ := hb
  let r : R := -(↑u⁻¹ * (W.a₁ * W.a₃ + 2 * W.a₄))
  let t : R := ↑u⁻¹ * (W.a₁ * W.a₄ - 2 * W.a₂ * W.a₃)
  have hr : r ∈ I ^ k := (I ^ k).neg_mem ((I ^ k).mul_mem_left _
    ((I ^ k).add_mem ((I ^ k).mul_mem_left _ h3) ((I ^ k).mul_mem_left _ h4)))
  have ht : t ∈ I ^ k := (I ^ k).mul_mem_left _
    ((I ^ k).sub_mem ((I ^ k).mul_mem_left _ h4) ((I ^ k).mul_mem_left _ h3))
  have hinv : (↑u⁻¹ : R) * W.b₂ = 1 := by rw [← hu, Units.inv_mul]
  have hlin3 : W.a₃ + r * W.a₁ + 2 * t = 0 := by
    dsimp only [r, t]
    rw [b₂] at hinv
    linear_combination -W.a₃ * hinv
  have hlin4 : W.a₄ + 2 * r * W.a₂ - t * W.a₁ = 0 := by
    dsimp only [r, t]
    rw [b₂] at hinv
    linear_combination -W.a₄ * hinv
  have hr2 : r ^ 2 ∈ I ^ (2 * k) := by
    simpa only [pow_two, two_mul, pow_add] using Ideal.mul_mem_mul hr hr
  have hr2' : r ^ 2 ∈ I ^ (k + 1) := Ideal.pow_le_pow_right (by omega) hr2
  have hrt : r * t ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul hr ht
  have hrA4 : r * W.a₄ ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul hr h4
  have htA3 : t * W.a₃ ∈ I ^ (2 * k) := by
    simpa only [two_mul, pow_add] using Ideal.mul_mem_mul ht h3
  have ht2 : t ^ 2 ∈ I ^ (2 * k) := by
    simpa only [pow_two, two_mul, pow_add] using Ideal.mul_mem_mul ht ht
  have ha4 : (VariableChange.mk 1 r 0 t • W).a₄ = 3 * r ^ 2 := by
    simp only [variableChange_def]
    simp
    linear_combination hlin4
  have hb2 : (VariableChange.mk 1 r 0 t • W).b₂ - W.b₂ = 12 * r := by
    simp [b₂, variableChange_def]
    ring
  have ha6 : (VariableChange.mk 1 r 0 t • W).a₆ - W.a₆ =
      r * W.a₄ + W.a₂ * r ^ 2 + r * r ^ 2 - t * W.a₃ - t ^ 2 - W.a₁ * (r * t) := by
    simp only [variableChange_def]
    simp
    ring
  refine ⟨r, t, hr, ht, ?_⟩
  dsimp only
  refine ⟨by simp [variableChange_def], ?_, ?_, ?_, ?_⟩
  · rw [hb2]
    exact (I ^ k).mul_mem_left _ hr
  · simpa [variableChange_def] using hlin3
  · rw [ha4]
    exact (I ^ (k + 1)).mul_mem_left _ hr2'
  · rw [ha6]
    exact (I ^ (2 * k)).sub_mem ((I ^ (2 * k)).sub_mem
      ((I ^ (2 * k)).sub_mem ((I ^ (2 * k)).add_mem
        ((I ^ (2 * k)).add_mem hrA4 ((I ^ (2 * k)).mul_mem_left _ hr2))
        ((I ^ (2 * k)).mul_mem_left _ hr2)) htA3) ht2)
      ((I ^ (2 * k)).mul_mem_left _ hrt)

end FLT.Mazur
