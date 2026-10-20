/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDepthStep
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Increase the depth of the second nodal coefficient

A shear with slope a₂/a₁ replaces a₂ by the negative square of the slope.
The first coefficient stays a unit over a local ring. No division by the
residue characteristic or completeness assumption is used.
-/

@[expose] public section
namespace FLT.Mazur
open WeierstrassCurve IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- A shear doubles the second coefficient depth and preserves the other node orders. -/
theorem exists_node_second_coefficient_step (h1 : IsUnit W.a₁)
    {k : ℕ} (hk : 1 ≤ k) (h2 : W.a₂ ∈ maximalIdeal R ^ k) :
    ∃ s : R, s ∈ maximalIdeal R ^ k ∧
      let V := VariableChange.mk 1 0 s 0 • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ^ (2 * k) ∧
        V.a₃ = W.a₃ ∧ V.a₄ = W.a₄ - s * W.a₃ ∧ V.a₆ = W.a₆ := by
  obtain ⟨u, hu⟩ := h1
  let s : R := ↑u⁻¹ * W.a₂
  have hs : s ∈ maximalIdeal R ^ k := (maximalIdeal R ^ k).mul_mem_left _ h2
  have hsI : s ∈ maximalIdeal R := Ideal.pow_le_self (by omega) hs
  have hs1 : s * W.a₁ = W.a₂ := by
    rw [← hu]
    dsimp only [s]
    rw [mul_comm (↑u⁻¹ * W.a₂), ← mul_assoc, Units.mul_inv, one_mul]
  have hs2 : s ^ 2 ∈ maximalIdeal R ^ (2 * k) := by
    simpa only [pow_two, two_mul, pow_add] using Ideal.mul_mem_mul hs hs
  have ha : IsUnit (W.a₁ + 2 * s) := by
    apply notMem_maximalIdeal.mp
    intro h
    have hbad := (maximalIdeal R).sub_mem h ((maximalIdeal R).mul_mem_left 2 hsI)
    exact (notMem_maximalIdeal.mpr (hu ▸ u.isUnit)) (by simpa using hbad)
  refine ⟨s, hs, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [variableChange_def] using ha
  · simpa [variableChange_def, hs1] using (maximalIdeal R ^ (2 * k)).neg_mem hs2
  all_goals simp [variableChange_def]

end FLT.Mazur
