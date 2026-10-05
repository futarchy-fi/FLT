/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodalDeterminantStep
public import FLT.Mazur.EllipticIntegralSingularTranslation
public import FLT.Mazur.EllipticCuspTangent

/-!
# Finite-depth normalization without a split tangent

A nodal special fiber has invertible b₂ after translating its singularity
to the origin. Iterating the determinant correction then deepens a₃,a₄
while retaining this unit and the special fiber. No tangent shear is used.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- At a normalized singularity, invertible c₄ implies invertible b₂. -/
theorem isUnit_b₂_of_normalized_node (h3 : W.a₃ ∈ maximalIdeal R)
    (h4 : W.a₄ ∈ maximalIdeal R) (hc : IsUnit W.c₄) : IsUnit W.b₂ := by
  apply (residue_ne_zero_iff_isUnit _).mp
  intro hz
  have he := normalized_c₄_eq_b₂_sq (W.map (residue R))
    ((residue_eq_zero_iff _).mpr h3) ((residue_eq_zero_iff _).mpr h4)
  rw [map_c₄, map_b₂, hz, zero_pow (by decide : 2 ≠ 0)] at he
  exact (residue_ne_zero_iff_isUnit _).mpr hc he

/-- Any normalized node can be translated to every finite a₃,a₄ depth. -/
theorem exists_nodal_depth_translation (hb : IsUnit W.b₂)
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R) (n : ℕ) :
    ∃ r t : R, r ∈ maximalIdeal R ∧ t ∈ maximalIdeal R ∧
      let V := VariableChange.mk 1 r 0 t • W
      IsUnit V.b₂ ∧ V.a₃ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal R ^ (n + 1) ∧ V.a₆ - W.a₆ ∈ maximalIdeal R ^ 2 := by
  induction n with
  | zero =>
    refine ⟨0, 0, (maximalIdeal R).zero_mem, (maximalIdeal R).zero_mem, ?_⟩
    simpa [variableChange_def] using And.intro hb (And.intro h3 h4)
  | succ n ih =>
    obtain ⟨r, t, hr, ht, hb', h3', h4', h6'⟩ := ih
    let V := VariableChange.mk 1 r 0 t • W
    obtain ⟨r', t', hr', ht', _, hb'', h3'', h4'', h6''⟩ :=
      exists_nodal_determinant_depth_step V (maximalIdeal R) hb' (by omega) h3' h4'
    have hcomp : VariableChange.mk 1 r' 0 t' • V =
        VariableChange.mk 1 (r + r') 0 (t + t') • W := by
      dsimp only [V]
      rw [← mul_smul]
      simp [VariableChange.mul_def, add_comm]
    have hrI : r' ∈ maximalIdeal R := Ideal.pow_le_self (by omega) hr'
    have htI : t' ∈ maximalIdeal R := Ideal.pow_le_self (by omega) ht'
    refine ⟨r + r', t + t', (maximalIdeal R).add_mem hr hrI,
      (maximalIdeal R).add_mem ht htI, ?_⟩
    dsimp only
    rw [← hcomp]
    refine ⟨?_, h3'' ▸ (maximalIdeal R ^ (n + 1 + 1)).zero_mem, h4'', ?_⟩
    · apply (residue_ne_zero_iff_isUnit _).mp
      have he := (residue_eq_zero_iff _).mpr (Ideal.pow_le_self (by omega) hb'')
      rw [map_sub, sub_eq_zero] at he
      rw [he]
      exact (residue_ne_zero_iff_isUnit _).mpr hb'
    · have h6small : (VariableChange.mk 1 r' 0 t' • V).a₆ - V.a₆ ∈
          maximalIdeal R ^ 2 := Ideal.pow_le_pow_right (by omega) h6''
      convert (maximalIdeal R ^ 2).add_mem h6small h6' using 1
      ring

/-- Every nodal equation admits a finite-depth translation, including nonsplit nodes. -/
theorem exists_integral_nodal_depth_normalization [PerfectField (ResidueField R)]
    (hΔ : W.Δ ∈ maximalIdeal R) (hc : IsUnit W.c₄) (n : ℕ) :
    ∃ r t : R, let V := VariableChange.mk 1 r 0 t • W
      IsUnit V.b₂ ∧ V.a₃ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal R ^ (n + 1) ∧ V.a₆ ∈ maximalIdeal R := by
  obtain ⟨r, t, h3, h4, h6⟩ := exists_integral_singular_translation W hΔ
  let V := VariableChange.mk 1 r 0 t • W
  have hc' : IsUnit V.c₄ := by simpa [V, integral_translation_c₄] using hc
  have hb := isUnit_b₂_of_normalized_node V h3 h4 hc'
  obtain ⟨r', t', _, _, hb', h3', h4', h6'⟩ := exists_nodal_depth_translation V hb h3 h4 n
  have hcomp : VariableChange.mk 1 r' 0 t' • V =
      VariableChange.mk 1 (r + r') 0 (t + t') • W := by
    dsimp only [V]
    rw [← mul_smul]
    simp [VariableChange.mul_def, add_comm]
  refine ⟨r + r', t + t', ?_⟩
  dsimp only
  rw [← hcomp]
  refine ⟨hb', h3', h4', ?_⟩
  have h6small := Ideal.pow_le_self (I := maximalIdeal R) (by decide : 2 ≠ 0) h6'
  convert (maximalIdeal R).add_mem h6small h6 using 1
  ring

end FLT.Mazur
