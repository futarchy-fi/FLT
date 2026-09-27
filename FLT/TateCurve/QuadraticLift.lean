/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.TateCurve.SymmetricInverse
public import FLT.TateCurve.Surjectivity

/-!
# Lifting symmetric Tate parameters

The analytic inverses reduce abscissa inversion to two quadratic equations.
A root automatically belongs to the required annulus and has the prescribed
Tate abscissa. Existence of roots over the original field remains a separate
arithmetic condition.
-/

@[expose] public section

open ValuativeRel

namespace TateCurve

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A root of the interior quadratic lies strictly between the two annulus boundaries. -/
theorem interior_quadratic_root_bounds {q t u : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) (ht : valuation K t < 1)
    (hroot : u ^ 2 - t * u + q = 0) :
    u ≠ 0 ∧ valuation K u < 1 ∧ valuation K (q / u) < 1 ∧ u + q / u = t := by
  have hu0 : u ≠ 0 := by
    intro h
    apply hq0
    simpa only [h, zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero, zero_add] using hroot
  have he : u * (t - u) = q := by linear_combination -hroot
  have hu : valuation K u < 1 := by
    by_contra h
    have hu : 1 ≤ valuation K u := le_of_not_gt h
    have htu : valuation K (t - u) = valuation K u :=
      (valuation K).map_sub_eq_of_lt_right (ht.trans_le hu)
    have hqge : 1 ≤ valuation K q := by
      rw [← he, map_mul, htu]
      simpa only [one_mul] using mul_le_mul' hu hu
    exact not_lt_of_ge hqge hq
  have hqu : q / u = t - u := by rw [← he, mul_div_cancel_left₀ _ hu0]
  exact ⟨hu0, hu, hqu ▸ (Valuation.map_sub _ _ _).trans_lt (max_lt ht hu),
    by rw [hqu]; ring⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A root of the boundary quadratic is a unit of valuation one, distinct from the pole. -/
theorem boundary_quadratic_root_bounds {z u : K} (hz0 : z ≠ 0)
    (hz : valuation K z ≤ 1) (hroot : u ^ 2 - (z + 2) * u + 1 = 0) :
    u ≠ 0 ∧ u ≠ 1 ∧ valuation K u = 1 ∧ u + u⁻¹ = z + 2 := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hroot
  have hu1 : u ≠ 1 := by intro h; subst u; apply hz0; linear_combination -hroot
  have he : u * (z + 2 - u) = 1 := by linear_combination -hroot
  have hs : valuation K (z + 2) ≤ 1 := (Valuation.map_add _ _ _).trans
    (max_le hz (valuation_natCast_le_one (R := K) 2))
  have hule : valuation K u ≤ 1 := by
    by_contra h
    have hu : 1 < valuation K u := lt_of_not_ge h
    have htu : valuation K (z + 2 - u) = valuation K u :=
      (valuation K).map_sub_eq_of_lt_right (hs.trans_lt hu)
    have hbad : 1 < valuation K (u * (z + 2 - u)) := by
      rw [map_mul, htu]
      exact hu.trans_le (le_mul_of_one_le_right' hu.le)
    simp [he] at hbad
  have huge : 1 ≤ valuation K u := by
    by_contra h
    have hu : valuation K u < 1 := lt_of_not_ge h
    have hsmall : valuation K (u * (z + 2 - u)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_right'
        ((Valuation.map_sub _ _ _).trans (max_le hs hu.le))).trans_lt hu
    simp [he] at hsmall
  refine ⟨hu0, hu1, le_antisymm hule huge, ?_⟩
  have hi : z + 2 - u = u⁻¹ := eq_inv_of_mul_eq_one_right he
  rw [← hi]
  ring

/-- An interior quadratic root realizes the abscissa specified by the symmetric inverse. -/
theorem tateX_eq_of_interior_quadratic {q t u x : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) (ht : valuation K t < 1)
    (hseries : (∑' n : ℕ, xPair (q ^ (2 * n) * q) (q ^ n * t)) -
      2 * tateCorrection q = x) (hroot : u ^ 2 - t * u + q = 0) :
    tateX u q = x := by
  obtain ⟨hu0, hu, hqu, he⟩ := interior_quadratic_root_bounds hq0 hq ht hroot
  rw [tateX_eq_tsum_xPair hq0 hu0 hq hu hqu, he]
  exact hseries

/-- A boundary quadratic root realizes the abscissa specified by the reciprocal inverse. -/
theorem tateX_eq_of_boundary_quadratic {q z u x : K} (hq0 : q ≠ 0)
    (hq : valuation K q < 1) (hz0 : z ≠ 0) (hz : valuation K z ≤ 1)
    (hseries : 1 / z + boundaryTail q z = x)
    (hroot : u ^ 2 - (z + 2) * u + 1 = 0) : tateX u q = x := by
  obtain ⟨hu0, hu1, hu, he⟩ := boundary_quadratic_root_bounds hz0 hz hroot
  have hterm : xTerm u = 1 / z := by
    have hden : (1 - u) ^ 2 = z * u := by linear_combination hroot
    rw [xTerm, hden]
    field_simp
  rw [tateX_eq_xTerm_add_tsum_xPair hq0 hu0 hq hu, he, hterm]
  simpa only [boundaryTail, add_sub_assoc] using hseries

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
/-- A normalized representative distinct from one cannot be a power of the Tate parameter. -/
theorem not_mem_zpowers_of_mem_annulus (q u : Kˣ)
    (hq : valuation K (q : K) < 1) (hu1 : (u : K) ≠ 1)
    (hlow : valuation K (q : K) < valuation K (u : K))
    (hupp : valuation K (u : K) ≤ 1) : u ∉ Subgroup.zpowers q := by
  intro h
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  have hpos : 0 < valuation K (q : K) :=
    zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr q.ne_zero)
  have hl : valuation K (q : K) < valuation K (q : K) ^ m := by
    simpa only [← hm, Units.val_zpow_eq_zpow_val, map_zpow₀] using hlow
  have hh : valuation K (q : K) ^ m ≤ 1 := by
    simpa only [← hm, Units.val_zpow_eq_zpow_val, map_zpow₀] using hupp
  have hm0 : 0 ≤ m := (zpow_le_one_iff_right_of_lt_one₀ hpos hq).mp hh
  have hm1 : m < 1 := (zpow_right_strictAnti₀ hpos hq).lt_iff_gt.mp (by simpa using hl)
  have hmz : m = 0 := by omega
  apply hu1
  rw [← hm, hmz, zpow_zero]
  rfl

/-- Rational roots of the two symmetric quadratics suffice for full Tate surjectivity. -/
theorem uniformizationPoint_surjective_of_quadratic_lifts (q : Kˣ)
    (hq : valuation K (q : K) < 1)
    (hi : ∀ x y t : K,
      (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y →
      valuation K x < 1 → valuation K t < 1 →
      (∑' n : ℕ, xPair ((q : K) ^ (2 * n) * q) ((q : K) ^ n * t)) -
        2 * tateCorrection (q : K) = x → ∃ u : K, u ^ 2 - t * u + q = 0)
    (hb : ∀ x y z : K,
      (WeierstrassCurve.tateCurve (q : K)).toAffine.Nonsingular x y →
      1 ≤ valuation K x → z ≠ 0 → valuation K z ≤ 1 →
      1 / z + boundaryTail (q : K) z = x →
        ∃ u : K, u ^ 2 - (z + 2) * u + 1 = 0) :
    Function.Surjective (uniformizationPoint q hq) := by
  apply uniformizationPoint_surjective_of_tateX q hq
  intro x y hxy
  rcases lt_or_ge (valuation K x) 1 with hx | hx
  · obtain ⟨t, ht, -⟩ := existsUnique_interior_symmetric_parameter hq hx
    obtain ⟨u, hroot⟩ := hi x y t hxy hx t.2 ht
    obtain ⟨hu0, hu, hqu, -⟩ := interior_quadratic_root_bounds q.ne_zero hq t.2 hroot
    refine ⟨Units.mk0 u hu0, ?_, tateX_eq_of_interior_quadratic q.ne_zero hq t.2 ht hroot⟩
    apply not_mem_zpowers_of_mem_annulus q (Units.mk0 u hu0) hq
      (by intro h; change u = 1 at h; simp [h] at hu) _ hu.le
    exact (div_lt_one₀ (zero_lt_iff.mpr ((valuation K).ne_zero_iff.mpr hu0))).mp
      (by simpa only [map_div₀] using hqu)
  · obtain ⟨z, hz0, hz, he⟩ := exists_boundary_symmetric_parameter hq hx
    obtain ⟨u, hroot⟩ := hb x y z hxy hx hz0 hz he
    obtain ⟨hu0, hu1, hu, -⟩ := boundary_quadratic_root_bounds hz0 hz hroot
    refine ⟨Units.mk0 u hu0, ?_, tateX_eq_of_boundary_quadratic q.ne_zero hq hz0 hz he hroot⟩
    apply not_mem_zpowers_of_mem_annulus q (Units.mk0 u hu0) hq hu1
    · simpa only [Units.val_mk0, hu] using hq
    · exact hu.le

end TateCurve
