/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionFinite
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Integral coordinates of prime-to-residue-characteristic torsion

Division polynomials force the coordinates of nonzero torsion points into an
integrally closed coefficient ring when the torsion order is a unit.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

/-- The x-coordinate of a nonzero torsion point belongs to the integrally closed
coefficient ring if its order is invertible there. -/
theorem exists_x_of_nsmul_eq_zero {R K : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]
    (W : WeierstrassCurve R) {n : ℕ} (hn : IsUnit (n : R)) {x y : K}
    (h : (W.map (algebraMap R K)).toAffine.Nonsingular x y)
    (hP : n • Affine.Point.some x y h = 0) :
    ∃ r : R, algebraMap R K r = x := by
  have hroot := (W.map (algebraMap R K)).isRoot_ΨSq_of_nsmul_eq_zero h n hP
  have heval : aeval x (W.ΨSq n) = 0 := by
    simpa only [WeierstrassCurve.map_ΨSq, Polynomial.IsRoot, eval_map, aeval_def] using hroot
  obtain ⟨u, hu⟩ := hn
  have hlead : (W.ΨSq (n : ℤ)).leadingCoeff = (n : R) ^ 2 := by
    simpa only [Int.cast_natCast] using
      W.leadingCoeff_ΨSq (n := (n : ℤ)) (by simpa only [Int.cast_natCast, ← hu] using u.ne_zero)
  have hint := isIntegral_leadingCoeff_smul (W.ΨSq n) x heval
  rw [hlead, ← hu] at hint
  have hint' := hint.smul (↑((u ^ 2)⁻¹) : R)
  simp only [smul_smul, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, one_smul] at hint'
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

/-- An affine point with integral x-coordinate also has integral y-coordinate
over an integrally closed coefficient ring. -/
theorem exists_y_of_equation {R K : Type*} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (x : R) {y : K}
    (h : (W.map (algebraMap R K)).toAffine.Equation (algebraMap R K x) y) :
    ∃ r : R, algebraMap R K r = y := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨X ^ 2 + C (W.a₁ * x + W.a₃) * X -
    C (x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆), by monicity!, ?_⟩
  have he := (Affine.equation_iff _ _).mp h
  simp only [WeierstrassCurve.map, WeierstrassCurve.toAffine] at he
  simpa [map_add, map_mul, map_pow, add_mul, sub_eq_zero, add_assoc] using he

/-- An addition slope is integral if both input x-coordinates and the output
x-coordinate are integral. -/
theorem exists_slope_of_addX {R K : Type*} [CommRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (W : WeierstrassCurve R) (x₁ x₂ z : R) {s : K}
    (h : (W.map (algebraMap R K)).toAffine.addX
      (algebraMap R K x₁) (algebraMap R K x₂) s = algebraMap R K z) :
    ∃ r : R, algebraMap R K r = s := by
  apply IsIntegrallyClosed.isIntegral_iff.mp
  refine ⟨X ^ 2 + C W.a₁ * X - C (W.a₂ + x₁ + x₂ + z), by monicity!, ?_⟩
  simp only [Affine.addX, WeierstrassCurve.map, WeierstrassCurve.toAffine] at h
  simp
  linear_combination h

/-- Prime-to-residue-characteristic torsion points whose reductions are opposite
at a nonsingular point are themselves opposite. -/
theorem torsion_add_eq_zero_of_reduction_eq_neg
    {R K k : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K] [Field k]
    (W : WeierstrassCurve R) (ρ : R →+* k) {n : ℕ} (hn : IsUnit (n : R))
    (x₁ x₂ y₁ y₂ : R)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (algebraMap R K x₁) (algebraMap R K y₁))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (algebraMap R K x₂) (algebraMap R K y₂))
    (hn₁ : n • Affine.Point.some _ _ h₁ = 0)
    (hn₂ : n • Affine.Point.some _ _ h₂ = 0)
    (hred : (W.map ρ).toAffine.Nonsingular (ρ x₁) (ρ y₁))
    (hx : ρ x₁ = ρ x₂)
    (hy : ρ y₁ = (W.map ρ).toAffine.negY (ρ x₂) (ρ y₂)) :
    Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂ = 0 := by
  let f := algebraMap R K
  let V := (W.map f).toAffine
  have hf : Function.Injective f := IsFractionRing.injective R K
  by_contra hsum
  have hxy : ¬(f x₁ = f x₂ ∧ f y₁ = V.negY (f x₂) (f y₂)) := by
    intro h
    exact hsum (Affine.Point.add_of_Y_eq h.1 h.2)
  have hsumtors : n • (Affine.Point.some _ _ h₁ + Affine.Point.some _ _ h₂) = 0 := by
    rw [nsmul_add, hn₁, hn₂, zero_add]
  rw [Affine.Point.add_some hxy] at hsumtors
  obtain ⟨z, hz⟩ := W.exists_x_of_nsmul_eq_zero hn _ hsumtors
  obtain ⟨s, hs⟩ := W.exists_slope_of_addX x₁ x₂ z hz.symm
  have he₁ : W.toAffine.Equation x₁ y₁ :=
    (W.toAffine.map_equation hf x₁ y₁).mp h₁.1
  have he₂ : W.toAffine.Equation x₂ y₂ :=
    (W.toAffine.map_equation hf x₂ y₂).mp h₂.1
  have hns := ((W.map ρ).toAffine.nonsingular_iff _ _).mp hred |>.2
  simp only [Affine.negY, WeierstrassCurve.map, WeierstrassCurve.toAffine] at hy hns
  by_cases hxeq : x₁ = x₂
  · have hyeq : y₁ = y₂ := hf <| Affine.Y_eq_of_Y_ne h₁.1 h₂.1 (congrArg f hxeq)
      (fun h ↦ hxy ⟨congrArg f hxeq, h⟩)
    subst x₂
    subst y₂
    have hden : f y₁ - V.negY (f x₁) (f y₁) ≠ 0 :=
      sub_ne_zero.mpr (fun h ↦ hxy ⟨rfl, h⟩)
    have ht : s * (2 * y₁ + W.a₁ * x₁ + W.a₃) =
        3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁ := by
      apply hf
      have ht := (eq_div_iff hden).mp
        (hs.trans (V.slope_of_Y_ne rfl (fun h ↦ hxy ⟨rfl, h⟩)))
      dsimp [V, Affine.negY, WeierstrassCurve.map, WeierstrassCurve.toAffine] at ht
      simp only [map_mul, map_add, map_ofNat, map_sub, map_pow]
      linear_combination ht
    have htρ := congrArg ρ ht
    simp only [map_mul, map_add, map_ofNat, map_sub, map_pow] at htρ
    rcases hns with hns | hns
    · apply hns
      have hd : 2 * ρ y₁ + ρ W.a₁ * ρ x₁ + ρ W.a₃ = 0 := by linear_combination hy
      rw [hd, mul_zero] at htρ
      linear_combination htρ
    · exact hns hy
  · have hline : s * (x₁ - x₂) = y₁ - y₂ := by
      apply hf
      simpa only [map_mul, map_sub] using
        (eq_div_iff (sub_ne_zero.mpr (fun h ↦ hxeq (hf h)))).mp
          (hs.trans (V.slope_of_X_ne (fun h ↦ hxeq (hf h))))
    have hsec : s * (y₁ + y₂ + W.a₁ * x₁ + W.a₃) + W.a₁ * y₂ =
        x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ := by
      apply (mul_left_cancel₀ (sub_ne_zero.mpr hxeq))
      rw [Affine.equation_iff] at he₁ he₂
      linear_combination he₁ - he₂ + (y₁ + y₂ + W.a₁ * x₁ + W.a₃) * hline
    have hlρ := congrArg ρ hline
    have hsρ := congrArg ρ hsec
    simp only [map_mul, map_add, map_sub, map_pow] at hlρ hsρ
    have hyρ : ρ y₁ = ρ y₂ := by rw [hx, sub_self, mul_zero] at hlρ; exact sub_eq_zero.mp hlρ.symm
    rw [← hx, ← hyρ] at hy hsρ
    have hd : ρ y₁ + ρ y₁ + ρ W.a₁ * ρ x₁ + ρ W.a₃ = 0 := by linear_combination hy
    rw [hd, mul_zero, zero_add] at hsρ
    rcases hns with hns | hns
    · apply hns
      linear_combination hsρ
    · exact hns hy

/-- Reduction is injective on integral prime-to-residue-characteristic torsion
whenever the common reduced point is nonsingular. -/
theorem torsion_eq_of_reduction_eq {R K k : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K] [Field k]
    (W : WeierstrassCurve R) (ρ : R →+* k) {n : ℕ} (hn : IsUnit (n : R))
    (x₁ x₂ y₁ y₂ : R)
    (h₁ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (algebraMap R K x₁) (algebraMap R K y₁))
    (h₂ : (W.map (algebraMap R K)).toAffine.Nonsingular
      (algebraMap R K x₂) (algebraMap R K y₂))
    (hn₁ : n • Affine.Point.some _ _ h₁ = 0)
    (hn₂ : n • Affine.Point.some _ _ h₂ = 0)
    (hred : (W.map ρ).toAffine.Nonsingular (ρ x₁) (ρ y₁))
    (hx : ρ x₁ = ρ x₂) (hy : ρ y₁ = ρ y₂) :
    Affine.Point.some _ _ h₁ = Affine.Point.some _ _ h₂ := by
  let hneg : (W.map (algebraMap R K)).toAffine.Nonsingular
      (algebraMap R K x₂) (algebraMap R K (W.toAffine.negY x₂ y₂)) := by
    rw [← W.toAffine.map_negY]
    exact (Affine.nonsingular_neg _ _).mpr h₂
  have heq : Affine.Point.some _ _ hneg = -Affine.Point.some _ _ h₂ := by
    simp only [Affine.Point.neg_some, ← W.toAffine.map_negY]
  apply sub_eq_zero.mp
  rw [sub_eq_add_neg, ← heq]
  apply W.torsion_add_eq_zero_of_reduction_eq_neg ρ hn x₁ x₂ y₁
    (W.toAffine.negY x₂ y₂) h₁ hneg hn₁
  · rw [heq, smul_neg, hn₂, neg_zero]
  · exact hred
  · exact hx
  · rw [← W.toAffine.map_negY, Affine.negY_negY, hy]

end WeierstrassCurve
