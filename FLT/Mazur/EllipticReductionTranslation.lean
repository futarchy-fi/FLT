/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticReductionRelation

/-!
# Integral translation by a point reducing to infinity

Cleared addition coordinates work for an arbitrary integral Weierstrass equation.
The integral point is allowed to have singular reduction. This stronger statement
also excludes an integral sum of two points reducing to infinity.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing WeierstrassCurve

variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A)

/-- Translation by a nonintegral point preserves integral affine coordinates
modulo the maximal ideal. -/
theorem exists_integral_add_nonintegral {x y : K} (u v : A)
    (hP : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hQ : (W.map (algebraMap A K)).toAffine.Nonsingular (u : K) (v : K))
    (hx : x ∉ A) :
    ∃ r s : A, ∃ h : (W.map (algebraMap A K)).toAffine.Nonsingular (r : K) (s : K),
      Affine.Point.some _ _ hP + .some _ _ hQ = .some _ _ h ∧
      residue A r = residue A u ∧ residue A s = residue A v := by
  obtain ⟨a, b, ha, hb, ha0, hb0⟩ := W.infinity_coordinates A hP.1 hx
  have hx0 : x ≠ 0 := fun he => hx (he ▸ A.zero_mem)
  have hxu : x ≠ (u : K) := fun he => hx (he ▸ u.property)
  have hunit : IsUnit (1 - a * u) := (residue_ne_zero_iff_isUnit _).mp (by simp [ha0])
  let d : A := ↑hunit.unit⁻¹
  let C : A := u ^ 2 + 2 * W.a₂ * u + W.a₄ - W.a₁ * v
  let D : A := 2 * W.a₆ + W.a₄ * u - W.a₃ * v
  let T : A := 2 * v + W.a₁ * u + W.a₃
  let c : A := 1 + W.a₂ * a + W.a₄ * a ^ 2 + W.a₆ * a ^ 3 - W.a₁ * b - W.a₃ * a * b
  let r : A := (u + a * C + a ^ 2 * D - b * T) * d ^ 2
  let s : A := (c * T - b * (2 * u ^ 2 + C) + a * b * (u ^ 3 - D)) * d ^ 3 +
    v * (a * r - 1) * d - W.a₁ * r - W.a₃
  have hd : algebraMap A K d = (1 - x⁻¹ * (u : K))⁻¹ := by
    simp only [d, map_units_inv, hunit.unit_spec, map_sub, map_one, map_mul,
      ValuationSubring.algebraMap_apply, ha]
  have hc : algebraMap A K c = y ^ 2 * x⁻¹ ^ 3 := by
    simp only [c, map_sub, map_add, map_one, map_mul, map_pow,
      ValuationSubring.algebraMap_apply, ha, hb]
    have hh := (Affine.equation_iff _ _).mp hP.1
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      ValuationSubring.algebraMap_apply] at hh
    field_simp
    linear_combination -hh
  have hr : (W.map (algebraMap A K)).toAffine.addX x u
      ((W.map (algebraMap A K)).toAffine.slope x u y v) = algebraMap A K r := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 (sub_ne_zero.mpr hxu)))
    rw [Affine.addX_cleared _ hP.1 hQ.1 hxu]
    simp only [r, map_mul, map_sub, map_add, map_pow, hd]
    simp only [C, D, T, map_mul, map_sub, map_add, map_pow, map_ofNat,
      map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, ValuationSubring.algebraMap_apply, ha, hb]
    field_simp
  have hs : (W.map (algebraMap A K)).toAffine.addY x u y
      ((W.map (algebraMap A K)).toAffine.slope x u y v) = algebraMap A K s := by
    have hh := Affine.addY_normalized _ hP.1 hQ.1 hx0 hxu
    dsimp only at hh
    simpa only [s, map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, hc, hd,
      C, D, T, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      ValuationSubring.algebraMap_apply, ha, hb, hr] using hh
  have hr0 : residue A r = residue A u := by
    simp [r, d, map_units_inv, ha0, hb0]
  have hs0 : residue A s = residue A v := by
    simp [s, c, T, d, map_units_inv, ha0, hb0, hr0]
    simp only [map_ofNat]
    ring
  have hns : (W.map (algebraMap A K)).toAffine.Nonsingular
      (algebraMap A K r) (algebraMap A K s) := by
    simpa only [hr, hs] using Affine.nonsingular_add hP hQ (fun h => hxu h.1)
  have he : Affine.Point.some _ _ (Affine.nonsingular_add hP hQ (fun h => hxu h.1)) =
      Affine.Point.some _ _ hns := by
    simp only [Affine.Point.some.injEq]
    exact ⟨hr, hs⟩
  exact ⟨r, s, hns, (Affine.Point.add_of_X_ne hxu).trans he, hr0, hs0⟩

/-- Translation by a point reducing to infinity preserves a smooth affine reduction. -/
theorem reducesTo_add_nonintegral_integral {x y : K} (u v : A)
    (hP : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hQ : (W.map (algebraMap A K)).toAffine.Nonsingular (u : K) (v : K))
    (hr : (W.map (residue A)).toAffine.Nonsingular (residue A u) (residue A v))
    (hx : x ∉ A) :
    ReducesTo A W (.some _ _ hP + .some _ _ hQ) (.some _ _ hr) := by
  obtain ⟨r, s, h, he, hr0, hs0⟩ := exists_integral_add_nonintegral A W u v hP hQ hx
  rw [he]
  change projectiveReduction A W _ = _
  rw [projectiveReduction_affine, hr0, hs0]
  rfl

end FLT.Mazur
