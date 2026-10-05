/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeCoordinateFactor
public import FLT.Mazur.EllipticNodeScaledEquation
public import FLT.Mazur.EllipticNormalizedSingularity

/-!
# Point branches from finite-depth nodal coefficients

For a principal maximal ideal, the deep coefficient conditions give the two
exclusive tangent branches below n/2 and two unit tangent factors at n/2.
Primitive scaled coordinates have smooth reduction exactly at depth zero.
Compatibility of these labels with point addition remains a separate proof.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R) {π : R}

/-- Below the middle depth an integral point lies on exactly one nodal tangent. -/
theorem node_point_branches_below_middle (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) (n k : ℕ) (hk : 1 ≤ k) (hkn : 2 * k < n)
    (h1 : IsUnit W.a₁) (h2 : W.a₂ ∈ maximalIdeal R)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (n + 1)) (h4 : W.a₄ ∈ maximalIdeal R ^ (n + 1))
    (h6 : W.a₆ ∈ maximalIdeal R ^ n) (x y : R) (hprim : IsUnit x ∨ IsUnit y)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    IsUnit x ∧
      ((y ∈ maximalIdeal R ∧ IsUnit (y + W.a₁ * x)) ∨
        (IsUnit y ∧ y + W.a₁ * x ∈ maximalIdeal R)) := by
  obtain ⟨b3, hb3, h3'⟩ := exists_node_deep_factor hgen k
    (Ideal.pow_le_pow_right (by omega) h3)
  obtain ⟨b4, hb4, h4'⟩ := exists_node_deep_factor hgen k
    (Ideal.pow_le_pow_right (by omega) h4)
  obtain ⟨b6, hb6, h6'⟩ := exists_node_deep_factor hgen (2 * k)
    (Ideal.pow_le_pow_right (by omega) h6)
  have hπm : π ∈ maximalIdeal R := hgen ▸ Ideal.mem_span_singleton_self π
  exact node_primitive_tangent_branches W h1 hprim
    (node_scaled_tangent_product W hπ hπm hk x y b3 b4 b6 h2 hb3 hb4 hb6 h3' h4' h6' he)

/-- At the exact middle depth the two scaled tangent factors are both units. -/
theorem node_point_units_at_middle (hπ : π ≠ 0)
    (hgen : maximalIdeal R = Ideal.span {π}) (k : ℕ) (hk : 1 ≤ k)
    (h2 : W.a₂ ∈ maximalIdeal R)
    (h3 : W.a₃ ∈ maximalIdeal R ^ (2 * k + 1))
    (h4 : W.a₄ ∈ maximalIdeal R ^ (2 * k + 1))
    (h6 : W.a₆ ∈ maximalIdeal R ^ (2 * k)) (h6' : W.a₆ ∉ maximalIdeal R ^ (2 * k + 1))
    (x y : R) (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    IsUnit y ∧ IsUnit (y + W.a₁ * x) := by
  obtain ⟨b3, hb3, h3e⟩ := exists_node_deep_factor hgen k
    (Ideal.pow_le_pow_right (by omega) h3)
  obtain ⟨b4, hb4, h4e⟩ := exists_node_deep_factor hgen k
    (Ideal.pow_le_pow_right (by omega) h4)
  obtain ⟨b6, h6e⟩ := exists_node_coordinate_factor hgen (2 * k) h6
  have hπm : π ∈ maximalIdeal R := hgen ▸ Ideal.mem_span_singleton_self π
  have hb6 : IsUnit b6 := by
    by_contra h
    apply h6'
    rw [h6e, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm (2 * k)) h
  exact node_scaled_middle_units W hπ hπm hk x y b3 b4 b6 h2 hb3 hb4 hb6 h3e h4e h6e he

omit [IsDomain R] in
/-- Primitive scaled coordinates reduce smoothly exactly when their common depth is zero. -/
theorem node_scaled_nonsingular_iff_depth_zero (hπm : π ∈ maximalIdeal R)
    (h3 : W.a₃ ∈ maximalIdeal R) (h4 : W.a₄ ∈ maximalIdeal R)
    (h6 : W.a₆ ∈ maximalIdeal R) (k : ℕ) (x y : R)
    (hprim : IsUnit x ∨ IsUnit y)
    (he : W.toAffine.Equation (π ^ k * x) (π ^ k * y)) :
    (W.map (residue R)).toAffine.Nonsingular
      (residue R (π ^ k * x)) (residue R (π ^ k * y)) ↔ k = 0 := by
  rw [normalized_nonsingular_iff (W.map (residue R))
    (by simpa using (residue_eq_zero_iff _).mpr h3)
    (by simpa using (residue_eq_zero_iff _).mpr h4)
    (by simpa using (residue_eq_zero_iff _).mpr h6) (he.map (residue R))]
  have hπ' := (residue_eq_zero_iff _).mpr hπm
  constructor
  · intro h
    by_contra hk
    exact h (by simp [hπ', hk])
  · rintro rfl h
    simp only [pow_zero, one_mul] at h
    rcases hprim with hx | hy
    · exact (residue_ne_zero_iff_isUnit _).mpr hx h.1
    · exact (residue_ne_zero_iff_isUnit _).mpr hy h.2

end FLT.Mazur
