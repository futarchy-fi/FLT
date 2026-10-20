/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeSecondCoefficientStep
public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# Finite normalization of the second split-node coefficient

Iterated integral shears make a₂ as deep as requested. The shear preserves
the exact constant coefficient and both higher linear coefficient orders,
so the original split-node depth survives. This is a finite construction.
-/

@[expose] public section
namespace FLT.Mazur
open WeierstrassCurve IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- A finite shear makes the second coefficient arbitrarily deep. -/
theorem exists_node_second_coefficient_normalization (h1 : IsUnit W.a₁)
    (h2 : W.a₂ ∈ maximalIdeal R) (n : ℕ) :
    ∃ s : R, s ∈ maximalIdeal R ∧
      let V := VariableChange.mk 1 0 s 0 • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₃ = W.a₃ ∧ V.a₄ = W.a₄ - s * W.a₃ ∧ V.a₆ = W.a₆ := by
  induction n with
  | zero =>
    refine ⟨0, (maximalIdeal R).zero_mem, ?_⟩
    simpa [variableChange_def] using And.intro h1 h2
  | succ n ih =>
    obtain ⟨s, hs, h1', h2', h3', h4', h6'⟩ := ih
    let V := VariableChange.mk 1 0 s 0 • W
    obtain ⟨t, ht, h1'', h2'', h3'', h4'', h6''⟩ :=
      exists_node_second_coefficient_step V h1' (by omega) h2'
    have hcomp : VariableChange.mk 1 0 t 0 • V =
        VariableChange.mk 1 0 (s + t) 0 • W := by
      dsimp only [V]
      rw [← mul_smul]
      simp [VariableChange.mul_def, add_comm]
    refine ⟨s + t, (maximalIdeal R).add_mem hs
      (Ideal.pow_le_self (by omega) ht), ?_⟩
    dsimp only
    rw [← hcomp]
    refine ⟨h1'', Ideal.pow_le_pow_right (by omega) h2'', h3''.trans h3', ?_,
      h6''.trans h6'⟩
    rw [h4'', h4', h3']
    ring

variable {W} {π : R} {m : ℕ}

/-- Normalizing a₂ retains the original exact split-node depth. -/
theorem SplitNodeDepth.exists_second_coefficient_normalization
    (D : SplitNodeDepth W π m) (n : ℕ) :
    ∃ s : R, s ∈ maximalIdeal R ∧
      SplitNodeDepth (VariableChange.mk 1 0 s 0 • W) π m ∧
      (VariableChange.mk 1 0 s 0 • W).a₂ ∈ maximalIdeal R ^ (n + 1) := by
  obtain ⟨s, hs, h1, h2, h3, h4, h6⟩ :=
    exists_node_second_coefficient_normalization W D.a₁_unit D.a₂_mem n
  refine ⟨s, hs, ?_, h2⟩
  refine ⟨D.depth_pos, D.uniformizer_ne_zero, D.maximalIdeal_eq, h1,
    Ideal.pow_le_self (by omega) h2, ?_, ?_, ?_, ?_⟩
  · rw [h3]
    exact D.a₃_mem
  · rw [h4]
    exact (maximalIdeal R ^ (m + 1)).sub_mem D.a₄_mem
      ((maximalIdeal R ^ (m + 1)).mul_mem_left s D.a₃_mem)
  · rw [h6]
    exact D.a₆_mem
  · rw [h6]
    exact D.a₆_not_mem

end FLT.Mazur
