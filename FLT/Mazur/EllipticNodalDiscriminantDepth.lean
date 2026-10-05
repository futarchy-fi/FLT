/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeDiscriminantDepth
public import FLT.Mazur.EllipticNodalDepthNormalization

/-!
# Discriminant depth for arbitrary nodal tangents

The unit b₂ suffices to identify the depth of a₆ with that of Δ. Combining
this observation with determinant normalization gives a finite-depth model
without a splitting hypothesis.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)

/-- The nodal discriminant factor is a unit whenever b₂ is a unit and a₆ reduces to zero. -/
theorem isUnit_nodal_discriminant_factor (hb : IsUnit W.b₂)
    (h6 : W.a₆ ∈ maximalIdeal R) : IsUnit (-W.b₂ ^ 3 - 432 * W.a₆) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  have hb' := (residue_ne_zero_iff_isUnit _).mpr hb
  have h6' := (residue_eq_zero_iff _).mpr h6
  simpa [h6'] using neg_ne_zero.mpr (pow_ne_zero 3 hb')

/-- At any normalized node, sufficiently deep a₃,a₄ equate the depths of Δ and a₆. -/
theorem nodal_discriminant_mem_pow_iff (hb : IsUnit W.b₂)
    (h6 : W.a₆ ∈ maximalIdeal R) (n : ℕ)
    (h3 : W.a₃ ∈ maximalIdeal R ^ n) (h4 : W.a₄ ∈ maximalIdeal R ^ n) :
    W.Δ ∈ maximalIdeal R ^ n ↔ W.a₆ ∈ maximalIdeal R ^ n := by
  have hcon := node_discriminant_congr W (maximalIdeal R ^ n) h3 h4
  have hu := isUnit_nodal_discriminant_factor W hb h6
  constructor
  · intro hd
    apply ((maximalIdeal R ^ n).mul_unit_mem_iff_mem hu).mp
    convert (maximalIdeal R ^ n).sub_mem hd hcon using 1
    ring
  · intro ha
    have hm := (maximalIdeal R ^ n).mul_mem_right (-W.b₂ ^ 3 - 432 * W.a₆) ha
    convert (maximalIdeal R ^ n).add_mem hcon hm using 1
    ring

/-- The exact discriminant depth determines a₆ depth without a rational tangent. -/
theorem nodal_a₆_exact_depth (hb : IsUnit W.b₂) (h6 : W.a₆ ∈ maximalIdeal R)
    (n : ℕ) (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1))
    (hd : W.Δ ∈ maximalIdeal R ^ n) (hd' : W.Δ ∉ maximalIdeal R ^ (n + 1)) :
    W.a₆ ∈ maximalIdeal R ^ n ∧ W.a₆ ∉ maximalIdeal R ^ (n + 1) := by
  exact ⟨(nodal_discriminant_mem_pow_iff W hb h6 n
    (Ideal.pow_le_pow_right (by omega) h3) (Ideal.pow_le_pow_right (by omega) h4)).mp hd,
    fun h => hd' ((nodal_discriminant_mem_pow_iff W hb h6 (n + 1) h3 h4).mpr h)⟩

/-- A nodal equation admits a translated model at its exact discriminant depth. -/
theorem exists_nodal_discriminant_depth [PerfectField (ResidueField R)]
    (n : ℕ) (hn : 1 ≤ n) (hd : W.Δ ∈ maximalIdeal R ^ n)
    (hd' : W.Δ ∉ maximalIdeal R ^ (n + 1)) (hc : IsUnit W.c₄) :
    ∃ r t : R, let V := VariableChange.mk 1 r 0 t • W
      IsUnit V.b₂ ∧ V.a₃ ∈ maximalIdeal R ^ (n + 1) ∧
        V.a₄ ∈ maximalIdeal R ^ (n + 1) ∧ V.a₆ ∈ maximalIdeal R ^ n ∧
          V.a₆ ∉ maximalIdeal R ^ (n + 1) := by
  obtain ⟨r, t, hb, h3, h4, h6⟩ := exists_integral_nodal_depth_normalization W
    (Ideal.pow_le_self (by omega) hd) hc n
  have hΔ : (VariableChange.mk 1 r 0 t • W).Δ = W.Δ := by
    simp [variableChange_Δ]
  exact ⟨r, t, hb, h3, h4,
    nodal_a₆_exact_depth _ hb h6 n h3 h4 (hΔ ▸ hd) (hΔ ▸ hd')⟩

end FLT.Mazur
