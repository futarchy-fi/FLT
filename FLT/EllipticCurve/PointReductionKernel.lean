/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.PointReductionAddition

/-!
# Translating a point that reduces to infinity

For a nonintegral affine point, `1/x` and `y/x²` lie in the maximal ideal.
Clearing the addition denominators in these coordinates proves that adding this
point to an integral affine point leaves its reduction unchanged.
-/

@[expose] public section

open Polynomial IsLocalRing
namespace WeierstrassCurve
variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Integral x-coordinates on an integral Weierstrass equation have integral y-coordinates. -/
theorem mem_y_of_mem_x {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  let a : A := ⟨x, hx⟩
  let f := W.toAffine.polynomial.map (evalRingHom a)
  have hf : f.Monic := Affine.monic_polynomial.map _
  have hy : IsIntegral A y := ⟨f, hf, by
    simpa [f, a, add_mul, ← add_assoc, eval₂_map, eval₂_evalRingHom,
      Affine.polynomial, Affine.equation_iff',
      eval₂_add, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] using h⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  exact hb ▸ b.property

/-- At a nonintegral affine point, `1/x` and `y/x²` are integral and reduce to zero. -/
theorem infinity_coordinates {x y : K}
    (h : (W.map (algebraMap A K)).toAffine.Equation x y) (hx : x ∉ A) :
    ∃ a b : A, (a : K) = x⁻¹ ∧ (b : K) = y * x⁻¹ ^ 2 ∧
      residue A a = 0 ∧ residue A b = 0 := by
  have hx0 : x ≠ 0 := fun he => hx (he ▸ A.zero_mem)
  let a : A := ⟨x⁻¹, (A.mem_or_inv_mem x).resolve_left hx⟩
  have ha : residue A a = 0 := by
    rw [residue_eq_zero_iff, ← ValuationSubring.coe_mem_nonunits_iff]
    exact A.inv_mem_nonunits_iff.mpr (Or.inr hx)
  let d : A := W.a₁ * a + W.a₃ * a ^ 2
  let e : A := a + W.a₂ * a ^ 2 + W.a₄ * a ^ 3 + W.a₆ * a ^ 4
  let f : A[X] := X ^ 2 + C d * X - C e
  have hf : f.Monic := by unfold f; monicity <;> norm_num
  have he : f.eval₂ (algebraMap A K) (y * x⁻¹ ^ 2) = 0 := by
    simp only [f, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
    simp only [d, e, map_add, map_mul, map_pow, ValuationSubring.algebraMap_apply]
    change (y * x⁻¹ ^ 2) ^ 2 + (↑W.a₁ * x⁻¹ + ↑W.a₃ * (x⁻¹) ^ 2) *
      (y * x⁻¹ ^ 2) - (x⁻¹ + ↑W.a₂ * (x⁻¹) ^ 2 + ↑W.a₄ * (x⁻¹) ^ 3 +
        ↑W.a₆ * (x⁻¹) ^ 4) = 0
    have hh := (Affine.equation_iff _ _).mp h
    simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
      ValuationSubring.algebraMap_apply] at hh
    field_simp
    linear_combination hh
  have hy : IsIntegral A (y * x⁻¹ ^ 2) := ⟨f, hf, he⟩
  obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hy
  have hfb : f.IsRoot b := by
    apply (IsFractionRing.injective A K)
    simpa only [map_zero, ← eval₂_at_apply, hb] using he
  have hr : (residue A b) ^ 2 = 0 := by
    have hh := hfb.map (f := residue A)
    simpa [f, d, e, IsRoot, ha] using hh
  exact ⟨a, b, rfl, hb, ha, sq_eq_zero_iff.mp hr⟩
end WeierstrassCurve

namespace WeierstrassCurve.Affine
variable {F : Type*} [Field F] [DecidableEq F] (E : WeierstrassCurve F)
  {x y u v : F}

/-- The addition x-coordinate after clearing the secant denominator and using both equations. -/
theorem addX_cleared (hP : E.toAffine.Equation x y) (hQ : E.toAffine.Equation u v)
    (hxu : x ≠ u) :
    (x - u) ^ 2 * E.toAffine.addX x u (E.toAffine.slope x u y v) =
      u * x ^ 2 + (u ^ 2 + 2 * E.a₂ * u + E.a₄ - E.a₁ * v) * x +
        (2 * E.a₆ + E.a₄ * u - E.a₃ * v) - y * (2 * v + E.a₁ * u + E.a₃) := by
  rw [addX_of_X_ne hxu, mul_div_cancel₀ _ (pow_ne_zero 2 (sub_ne_zero.mpr hxu))]
  have hp := (equation_iff _ _).mp hP
  have hq := (equation_iff _ _).mp hQ
  linear_combination hp + hq

/-- The addition y-coordinate in the normalized coordinates `1/x` and `y/x²`. -/
theorem addY_normalized (hP : E.toAffine.Equation x y) (hQ : E.toAffine.Equation u v)
    (hx : x ≠ 0) (hxu : x ≠ u) :
    let a := x⁻¹
    let b := y * a ^ 2
    let c := y ^ 2 * a ^ 3
    let d := (1 - a * u)⁻¹
    let C := u ^ 2 + 2 * E.a₂ * u + E.a₄ - E.a₁ * v
    let D := 2 * E.a₆ + E.a₄ * u - E.a₃ * v
    let T := 2 * v + E.a₁ * u + E.a₃
    let r := E.toAffine.addX x u (E.toAffine.slope x u y v)
    E.toAffine.addY x u y (E.toAffine.slope x u y v) =
      (c * T - b * (2 * u ^ 2 + C) + a * b * (u ^ 3 - D)) * d ^ 3 +
        v * (a * r - 1) * d - E.a₁ * r - E.a₃ := by
  dsimp only
  have hd : 1 - x⁻¹ * u ≠ 0 := by
    intro he
    apply hxu
    field_simp at he
    linear_combination he
  have hr := addX_cleared E hP hQ hxu
  rw [addY, negY, negAddY, slope_of_X_ne hxu]
  rw [slope_of_X_ne hxu] at hr
  field_simp
  linear_combination -y * hr
end WeierstrassCurve.Affine

open Polynomial IsLocalRing
namespace WeierstrassCurve
variable {K : Type*} [Field K] [DecidableEq K] (A : ValuationSubring K)
  (W : WeierstrassCurve A) [(W.map (residue A)).IsElliptic]

/-- Adding a nonintegral affine point to an integral affine point preserves the latter reduction. -/
theorem reducePoint_add_nonintegral_integral {x y : K} (u v : A)
    (hP : (W.map (algebraMap A K)).toAffine.Nonsingular x y)
    (hQ : (W.map (algebraMap A K)).toAffine.Nonsingular (u : K) (v : K))
    (hx : x ∉ A) :
    W.reducePoint A (.some _ _ hP + .some _ _ hQ) = W.reducePoint A (.some _ _ hQ) := by
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
  rw [Affine.Point.add_of_X_ne hxu, he]
  have hh := W.reducePoint_some A r s hns
  have hq := W.reducePoint_some A u v hQ
  rw [hq]
  exact hh.trans (by
    simp only [Affine.Point.some.injEq]
    exact ⟨hr0, hs0⟩)
end WeierstrassCurve
