/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDepthStep
public import FLT.Mazur.EllipticIntegralNodeNormalization

/-!
# Finite-depth normalization of a split node

Iterating integral translations makes a₃ and a₄ arbitrarily deep without
changing a₁ or the discriminant. The accumulated translation stays in the
maximal ideal and a₆ changes only in its square. Completeness is not needed
for any prescribed finite depth.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- A normalized node can be translated to every finite coefficient depth. -/
theorem exists_node_depth_translation (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ I)
    (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (n : ℕ) :
    ∃ r t : R, r ∈ I ∧ t ∈ I ∧
      let V := VariableChange.mk 1 r 0 t • W
      V.a₁ = W.a₁ ∧ V.a₂ ∈ I ∧ V.a₃ ∈ I ^ (n + 1) ∧ V.a₄ ∈ I ^ (n + 1) ∧
        V.a₆ - W.a₆ ∈ I ^ 2 := by
  induction n with
  | zero =>
    refine ⟨0, 0, I.zero_mem, I.zero_mem, ?_⟩
    simpa [variableChange_def] using And.intro h2 (And.intro h3 h4)
  | succ n ih =>
    obtain ⟨r, t, hr, ht, h1', h2', h3', h4', h6'⟩ := ih
    let V := VariableChange.mk 1 r 0 t • W
    obtain ⟨r', t', hr', ht', h1'', h2'', h3'', h4'', h6''⟩ :=
      exists_node_depth_step V I (h1' ▸ h1) h2' (by omega) h3' h4'
    have hcomp : VariableChange.mk 1 r' 0 t' • V =
        VariableChange.mk 1 (r + r') 0 (t + t') • W := by
      dsimp only [V]
      rw [← mul_smul]
      simp [VariableChange.mul_def, add_comm]
    have hrI : r' ∈ I := Ideal.pow_le_self (by omega) hr'
    have htI : t' ∈ I := Ideal.pow_le_self (by omega) ht'
    refine ⟨r + r', t + t', I.add_mem hr hrI, I.add_mem ht htI, ?_⟩
    dsimp only
    rw [← hcomp]
    refine ⟨h1''.trans h1', h2'', h3'' ▸ (I ^ (n + 1 + 1)).zero_mem, h4'', ?_⟩
    have h6small : (VariableChange.mk 1 r' 0 t' • V).a₆ - V.a₆ ∈ I ^ 2 :=
      Ideal.pow_le_pow_right (by omega) h6''
    convert (I ^ 2).add_mem h6small h6' using 1
    ring

/-- The split-node input admits every finite a₃,a₄ depth, with a₁ still a unit. -/
theorem exists_integral_node_depth_normalization [IsLocalRing R]
    [PerfectField (ResidueField R)] (hΔ : W.Δ ∈ maximalIdeal R) (hc : IsUnit W.c₄)
    (hsplit : (W.nodePoly.map (residue R)).Splits) (n : ℕ) :
    ∃ r s t : R, let V := VariableChange.mk 1 r s t • W
      IsUnit V.a₁ ∧ V.a₂ ∈ maximalIdeal R ∧ V.a₃ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal R ^ (n + 1) ∧ V.a₆ ∈ maximalIdeal R := by
  obtain ⟨r, s, t, h1, h2, h3, h4, h6⟩ :=
    exists_integral_node_normalization W hΔ hc hsplit
  let V := VariableChange.mk 1 r s t • W
  obtain ⟨r', t', _, _, h1', h2', h3', h4', h6'⟩ :=
    exists_node_depth_translation V (maximalIdeal R) h1 h2 h3 h4 n
  have hcomp : VariableChange.mk 1 r' 0 t' • V =
      VariableChange.mk 1 (r + r') s (s * r' + t + t') • W := by
    dsimp only [V]
    rw [← mul_smul]
    simp [VariableChange.mul_def, add_comm, add_left_comm, mul_comm]
  refine ⟨r + r', s, s * r' + t + t', ?_⟩
  dsimp only
  rw [← hcomp]
  refine ⟨h1' ▸ h1, h2', h3', h4', ?_⟩
  have h6small := Ideal.pow_le_self (I := maximalIdeal R) (by decide : 2 ≠ 0) h6'
  convert (maximalIdeal R).add_mem h6small h6 using 1
  ring

end FLT.Mazur
