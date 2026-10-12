/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedDepthData
public import FLT.Mazur.NodeTangentDepth

/-!
# Divided coefficients from the original nonsplit depth conditions

These cancellations use the original maximal-ideal powers, without assuming
that a tangent is rational or that a₁ is a unit. They therefore apply before
adjoining the nonsplit tangent root and before shearing the original equation.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {depth k : ℕ}

include hπ hm in
/-- Cancel an original uniformizer power without a split-node hypothesis. -/
theorem nodalDepth_cancel {b : R} (s t : ℕ)
    (h : π ^ s * b ∈ maximalIdeal R ^ (s + t)) :
    b ∈ maximalIdeal R ^ t := by
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h ⊢
  obtain ⟨c, hc⟩ := h
  refine ⟨c, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero s hπ)
  simpa only [pow_add, mul_assoc] using hc

omit [IsDomain R] in
include hm in
/-- The original depth conditions construct all three divided coefficients. -/
theorem nodalDepth_exists_data (hk : 2 * k ≤ depth)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
    (h6 : W.a₆ ∈ maximalIdeal R ^ depth) : Nonempty (Data W π k) := by
  have g3 := Ideal.pow_le_pow_right (by omega : k ≤ depth + 1) h3
  have g4 := Ideal.pow_le_pow_right (by omega : k ≤ depth + 1) h4
  have g6 := Ideal.pow_le_pow_right hk h6
  rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at g3 g4 g6
  obtain ⟨b3, hb3⟩ := g3
  obtain ⟨b4, hb4⟩ := g4
  obtain ⟨b6, hb6⟩ := g6
  exact ⟨⟨b3, b4, b6, hb3, hb4,
    by simpa only [← pow_mul, Nat.mul_comm k 2] using hb6⟩⟩

include hπ hm in
/-- Both actual divided linear coefficients vanish before any tangent extension. -/
theorem nodalDepth_linear_mem (d : Data W π k) (hk : 2 * k ≤ depth)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) :
    d.b3 ∈ maximalIdeal R ∧ d.b4 ∈ maximalIdeal R := by
  have hle : maximalIdeal R ^ (depth + 1) ≤ maximalIdeal R ^ (k + 1) :=
    Ideal.pow_le_pow_right (by omega)
  constructor
  · simpa using nodalDepth_cancel hπ hm k 1 (d.factor3 ▸ hle h3)
  · simpa using nodalDepth_cancel hπ hm k 1 (d.factor4 ▸ hle h4)

include hπ hm in
/-- Strictly below the middle depth the original divided constant has zero residue. -/
theorem nodalDepth_constant_mem (d : Data W π k) (hk : 2 * k < depth)
    (h6 : W.a₆ ∈ maximalIdeal R ^ depth) : d.b6 ∈ maximalIdeal R := by
  have h : π ^ (2 * k) * d.b6 ∈ maximalIdeal R ^ (2 * k + 1) := by
    have hle := Ideal.pow_le_pow_right (by omega : 2 * k + 1 ≤ depth) h6
    simpa only [d.factor6, ← pow_mul, Nat.mul_comm k 2] using hle
  simpa using nodalDepth_cancel hπ hm (2 * k) 1 h

omit [IsDomain R] in
include hm in
/-- At exact equality depth the original divided constant is a unit. -/
theorem nodalDepth_constant_isUnit (d : Data W π k) (hk : 2 * k = depth)
    (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) : IsUnit d.b6 := by
  rw [← notMem_maximalIdeal]
  intro hb
  apply h6
  rw [d.factor6, ← pow_mul, Nat.mul_comm k 2, hk]
  have hp : π ^ depth ∈ maximalIdeal R ^ depth := by
    rw [hm, Ideal.span_singleton_pow]
    exact Ideal.subset_span (Set.mem_singleton _)
  simpa only [pow_succ] using Ideal.mul_mem_mul hp hb

omit [IsDomain R] in
include hm in
/-- The original uniformizer vanishes in the residue field. -/
theorem nodalDepth_residue_uniformizer : residue R π = 0 :=
  (residue_eq_zero_iff π).mpr (hm ▸ Ideal.mem_span_singleton_self π)

end FLT.Mazur.WeierstrassDividedDepth
