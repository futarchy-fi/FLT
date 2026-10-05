/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalCoordinates

/-!
# Integral negation in the formal infinity chart

Weierstrass negation sends [t : -1 : s] to [t : 1-a₁t-a₃s : s].
The middle coordinate is a unit at the origin, giving integral normalized
coordinates for the inverse point.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity

variable {R : Type*} [CommRing R] {σ : Type*}

/-- The normalizing denominator for Weierstrass negation. -/
def negationDenominator (W : WeierstrassCurve R) (t s : R) : R :=
  1 - W.a₁ * t - W.a₃ * s

/-- Negation preserves the infinity equation after normalization by a unit. -/
theorem equation_negation (W : WeierstrassCurve R) {t s u : R}
    (hs : Equation W t s) (hu : negationDenominator W t s * u = 1) :
    Equation W (-t * u) (-s * u) := by
  unfold Equation at hs ⊢
  unfold negationDenominator at hu
  linear_combination -u ^ 3 * hs + s * u * (1 + u) * hu

/-- Integral inverse of the normalizing denominator in the formal chart. -/
noncomputable def negationUnitInv (W : WeierstrassCurve R) (t : MvPowerSeries σ R) :
    MvPowerSeries σ R :=
  MvPowerSeries.invOfUnit (negationDenominator (curve W) t (coordinate W t)) 1

/-- Formal parameter of the negative point. -/
noncomputable def negate (W : WeierstrassCurve R) (t : MvPowerSeries σ R) :
    MvPowerSeries σ R := -t * negationUnitInv W t

/-- The normalizing denominator is one at the origin. -/
@[simp] theorem constantCoeff_negationDenominator (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (negationDenominator (curve W) t (coordinate W t)).constantCoeff = 1 := by
  simp [negationDenominator, curve, ht, constantCoeff_coordinate W ht]

/-- The constructed inverse really inverts the normalizing denominator. -/
theorem negationDenominator_mul_inv (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    negationDenominator (curve W) t (coordinate W t) * negationUnitInv W t = 1 :=
  MvPowerSeries.mul_invOfUnit _ 1 (constantCoeff_negationDenominator W ht)

/-- Negation preserves the formal neighborhood of infinity. -/
@[simp] theorem constantCoeff_negate (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    (negate W t).constantCoeff = 0 := by
  simp [negate, ht]

/-- The s-coordinate of the inverse is given by the same integral series. -/
theorem coordinate_negate (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) :
    coordinate W (negate W t) = -coordinate W t * negationUnitInv W t := by
  symm
  apply eq_coordinate W (constantCoeff_negate W ht)
  · simp [constantCoeff_coordinate W ht]
  · exact equation_negation (curve W) (equation_coordinate W ht)
      (negationDenominator_mul_inv W ht)

/-- Normalized negation applied twice returns the original parameter. -/
theorem negate_negate (W : WeierstrassCurve R)
    {t : MvPowerSeries σ R} (ht : t.constantCoeff = 0) : negate W (negate W t) = t := by
  have h₁ := negationDenominator_mul_inv W ht
  have h₂ := negationDenominator_mul_inv W (constantCoeff_negate W ht)
  rw [coordinate_negate W ht] at h₂
  simp only [negate, negationDenominator] at h₁ h₂ ⊢
  linear_combination t * h₂ + t * negationUnitInv W (-t * negationUnitInv W t) * h₁

end FLT.Mazur.FormalInfinity
