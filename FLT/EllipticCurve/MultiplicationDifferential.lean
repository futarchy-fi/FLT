/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.InvariantDifferential
public import FLT.EllipticCurve.DivisionPolynomialDifferential
/-!
# Differentiating multiplication on the universal curve

The invariant derivation sends the coordinates of `[n]P` to `n` times the
invariant vector field at `[n]P`. The proof uses the affine addition formulas,
with a separate tangent calculation for doubling.
-/

@[expose] public section

namespace WeierstrassCurve.Universal
open Polynomial
open WeierstrassCurve.Affine

/-- The invariant derivation of the universal pointed curve. -/
noncomputable abbrev invD := curve.fractionDeriv

/-- The invariant derivation is induced by the polynomial vector field. -/
lemma invD_poly (p : Poly) : invD (polyToField p) = polyToField (curve.polyDeriv p) := by
  rw [polyToField_apply, Affine.fractionDeriv_algebraMap, Affine.coordDeriv_mk]
  rfl

/-- On polynomials in `X`, the invariant derivation is `ψ₂` times differentiation. -/
lemma invD_C (p : (MvPolynomial Coeff ℤ)[X]) :
    invD (polyToField (C p)) = polyToField curve.ψ₂ * polyToField (C p.derivative) := by
  rw [invD_poly, Affine.polyDeriv_C, map_mul]
  rfl

/-- The invariant derivation annihilates the coefficient ring. -/
lemma invD_coeff (a : MvPolynomial Coeff ℤ) : invD (polyToField (C (C a))) = 0 := by
  simp [invD_C]

/-- The invariant derivation of the first coordinate of the universal point. -/
lemma invD_x : invD (Affine.smulX 1) =
    2 * Affine.smulY 1 + pointedCurve.a₁ * Affine.smulX 1 + pointedCurve.a₃ := by
  simp only [Affine.smulX_one, invD_C, derivative_X, map_one, mul_one,
    Affine.smulY_one, pointedCurve_a₁, pointedCurve_a₃, ψ₂, Affine.polynomialY,
    map_add, map_mul, map_ofNat]
  ring

/-- The invariant derivation of the second coordinate of the universal point. -/
lemma invD_y : invD (Affine.smulY 1) =
    3 * (Affine.smulX 1) ^ 2 + 2 * pointedCurve.a₂ * Affine.smulX 1 + pointedCurve.a₄ - 
      pointedCurve.a₁ * Affine.smulY 1 := by
  simp only [Affine.smulY_one, invD_poly, Affine.polyDeriv_X, map_neg,
    Affine.polynomialX, map_sub, map_mul, map_pow, map_add, map_ofNat,
    Affine.smulX_one, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₄]
  ring

/-- The affine addition formulas compute the sum of two distinct multiples. -/
lemma smul_add_coordinates {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0)
    (hs : m + n ≠ 0) (hx : Affine.smulX m ≠ Affine.smulX n) :
    let E := pointedCurve.toAffine
    let l := E.slope (Affine.smulX m) (Affine.smulX n) (Affine.smulY m) (Affine.smulY n)
    Affine.smulX (m + n) = E.addX (Affine.smulX m) (Affine.smulX n) l ∧
    Affine.smulY (m + n) = E.addY (Affine.smulX m) (Affine.smulX n) (Affine.smulY m) l := by
  classical
  obtain ⟨h₁, e₁⟩ := Affine.zsmul_point_eq_smulX_smulY hm
  obtain ⟨h₂, e₂⟩ := Affine.zsmul_point_eq_smulX_smulY hn
  obtain ⟨h₃, e₃⟩ := Affine.zsmul_point_eq_smulX_smulY hs
  rw [add_zsmul, e₁, e₂, WeierstrassCurve.Affine.Point.add_of_X_ne hx,
    WeierstrassCurve.Affine.Point.some_eq_some_iff] at e₃
  exact ⟨e₃.1.symm, e₃.2.symm⟩

/-- Multiplication by a positive integer multiplies the invariant speed by that integer. -/
lemma invD_smul (n : ℕ) (hn : n ≠ 0) :
    invD (Affine.smulX n) = (n : Universal.Field) * 
      (2 * Affine.smulY n + pointedCurve.a₁ * Affine.smulX n + pointedCurve.a₃) ∧
    invD (Affine.smulY n) = (n : Universal.Field) * 
      (3 * (Affine.smulX n) ^ 2 + 2 * pointedCurve.a₂ * Affine.smulX n + pointedCurve.a₄ - 
        pointedCurve.a₁ * Affine.smulY n) := by
  classical
  have ha₁ : invD pointedCurve.a₁ = 0 := invD_coeff _
  have ha₂ : invD pointedCurve.a₂ = 0 := invD_coeff _
  have ha₃ : invD pointedCurve.a₃ = 0 := invD_coeff _
  have ha₄ : invD pointedCurve.a₄ = 0 := invD_coeff _
  induction n using Nat.strong_induction_on with
  | h n ih =>
    obtain _|_|_|n := n
    · exact (hn rfl).elim
    · simpa only [Nat.reduceAdd, Nat.cast_one, one_mul] using And.intro invD_x invD_y
    · have hx := pointedCurve.toAffine.deriv_doubleX invD Affine.smulY_one_ne_negY
        ha₁ ha₂ ha₃ ha₄ (m := 1) (by simpa using invD_x) (by simpa using invD_y)
      have hy := pointedCurve.toAffine.deriv_doubleY invD Affine.smulY_one_ne_negY
        ha₁ ha₂ ha₃ ha₄ (m := 1) (by simpa using invD_x) (by simpa using invD_y)
      change invD (Affine.smulX 2) = _ ∧ invD (Affine.smulY 2) = _
      simpa only [show pointedCurve.toAffine.slope (Affine.smulX 1) (Affine.smulX 1)
          (Affine.smulY 1) (Affine.smulY 1) = Affine.slopeOne from rfl,
            Affine.addX_smul_one_smul_one,
        Affine.addY_smul_one_smul_one, mul_one, Nat.reduceAdd, Nat.cast_ofNat] using And.intro hx hy
    · obtain ⟨dx, dy⟩ := ih (n + 2) (by omega) (by omega)
      have hx : Affine.smulX (n + 2 : ℕ) ≠ Affine.smulX 1 :=
        Affine.smulX_ne_smulX (by omega) (by omega)
      have hc := smul_add_coordinates (m := (n + 2 : ℕ)) (n := 1)
        (by omega) one_ne_zero (by omega) hx
      have dhx := pointedCurve.toAffine.deriv_addX invD
        (Affine.nonsingular_smulX_smulY (n := (n + 2 : ℕ)) (by omega)).1
        (Affine.nonsingular_smulX_smulY (n := 1) one_ne_zero).1 hx ha₁ ha₂ dx dy (m := (n + 2 :
          ℕ)) (n := 1)
        (by simpa using invD_x) (by simpa using invD_y)
      have dhy := pointedCurve.toAffine.deriv_addY invD
        (Affine.nonsingular_smulX_smulY (n := (n + 2 : ℕ)) (by omega)).1
        (Affine.nonsingular_smulX_smulY (n := 1) one_ne_zero).1 hx ha₁ ha₂ ha₃ dx dy (m := (n + 2
          : ℕ)) (n := 1)
        (by simpa using invD_x) (by simpa using invD_y)
      dsimp only at hc dhx dhy
      rw [← hc.1, ← hc.2] at dhx dhy
      convert And.intro dhx dhy using 1 <;> push_cast <;> ring_nf

/-- The inclusion of univariate polynomials in the universal function field. -/
noncomputable abbrev xToField : (MvPolynomial Coeff ℤ)[X] →+* Universal.Field :=
  polyToField.comp C

/-- Univariate polynomials inject into the universal function field. -/
lemma xToField_injective : Function.Injective xToField :=
  (IsFractionRing.injective Universal.Ring Universal.Field).comp
    (WeierstrassCurve.Affine.CoordinateRing.algebraMap_poly_injective (W' := curve))

/-- The square division polynomial becomes the square of the division function. -/
lemma xToField_ΨSq (n : ℤ) : xToField (curve.ΨSq n) = ψᵤ n ^ 2 := by
  have h := congrArg (algebraMap Universal.Ring Universal.Field)
    (WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq curve n)
  simpa only [map_pow, ← WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
    WeierstrassCurve.Affine.CoordinateRing.mk, xToField, RingHom.comp_apply,
    polyToField_apply] using h.symm

/-- The univariate multiplication numerator agrees with the bivariate numerator. -/
lemma xToField_Φ (n : ℤ) : xToField (curve.Φ n) = polyToField (curve.φ n) := by
  exact (congrArg (algebraMap Universal.Ring Universal.Field)
    (WeierstrassCurve.Affine.CoordinateRing.mk_φ curve n)).symm

/-- The invariant derivation sends `ψ₂` to the invariant polynomial. -/
lemma invD_ψ₂ : invD (ψᵤ 2) = xToField curve.invar := by
  have h := congrArg invD Affine.smulY_one_sub_negY
  simp only [Affine.negY, map_sub, map_neg, invD_x, invD_y,
    invD.leibniz, show invD pointedCurve.a₁ = 0 from invD_coeff _,
    show invD pointedCurve.a₃ = 0 from invD_coeff _, smul_eq_mul] at h
  rw [← h]
  simp only [xToField, RingHom.comp_apply, invar, b₂, b₄, map_add, map_mul,
    map_pow, map_ofNat, pointedCurve_a₁, pointedCurve_a₂, pointedCurve_a₃,
    pointedCurve_a₄, Affine.smulX_one]
  ring
end WeierstrassCurve.Universal


