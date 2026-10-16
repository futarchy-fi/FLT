/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralChart
public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# A unit denominator on the entire arithmetic infinity chart

The original cubic writes Z/Y times a denominator as (X/Y)^3. When the
non-tangent coefficients lie in a nilpotent ideal, that denominator is a unit
on the entire infinity chart, including its section at infinity.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
local notation "B" => Coordinate W 1
local notation "u" => coord W 1 0
local notation "w" => coord W 1 2
local notation "c" => algebraMap R B

/-- The full denominator obtained by grouping the original homogeneous cubic by Z/Y. -/
def nilpotentInfinityDenominator : B :=
  1 + c W.a₁ * u + c W.a₃ * w - c W.a₂ * u ^ 2 -
    c W.a₄ * u * w - c W.a₆ * w ^ 2

/-- The denominator retains every coefficient of the original infinity equation. -/
theorem nilpotentInfinityDenominator_cubic : w * nilpotentInfinityDenominator W = u ^ 3 := by
  have h := coord_equation W 1
  rw [WeierstrassCurve.Projective.equation_iff] at h
  simp only [coord_self, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
  dsimp only [nilpotentInfinityDenominator]
  linear_combination h

variable (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "J" => I.map c

include h2 h3 h4 h6 in
/-- The correction to the split denominator belongs to the original extended arithmetic ideal. -/
theorem nilpotentInfinityDenominator_correction_mem :
    nilpotentInfinityDenominator W - (1 + c W.a₁ * u) ∈ J := by
  have he : nilpotentInfinityDenominator W - (1 + c W.a₁ * u) =
      c W.a₃ * w - c W.a₂ * u ^ 2 - c W.a₄ * u * w - c W.a₆ * w ^ 2 := by
    unfold nilpotentInfinityDenominator
    ring
  rw [he]
  exact (J).sub_mem ((J).sub_mem ((J).sub_mem
    ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h3))
    ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h2)))
    ((J).mul_mem_right _ ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h4))))
    ((J).mul_mem_right _ (Ideal.mem_map_of_mem c h6))

include hI h2 h3 h4 h6 in
/-- The full original infinity denominator is invertible, without removing any infinity point. -/
theorem nilpotentInfinityDenominator_isUnit : IsUnit (nilpotentInfinityDenominator W) := by
  let d := nilpotentInfinityDenominator W
  let e := d - (1 + c W.a₁ * u)
  let b := 1 - c W.a₁ * u + (c W.a₁) ^ 2 * u ^ 2
  have he : IsNilpotent e := NilpotentQuadraticRoot.element_nilpotent J
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI c)
    (nilpotentInfinityDenominator_correction_mem W I h2 h3 h4 h6)
  have hn : IsNilpotent (e * b) := (Commute.all e b).isNilpotent_mul_right he
  have hu : IsUnit (1 + e * b) := hn.isUnit_add_left_of_commute isUnit_one (mul_comm _ _)
  have hid : d * (b - (c W.a₁) ^ 3 * w) = 1 + e * b := by
    have hc := nilpotentInfinityDenominator_cubic W
    dsimp only [d, e, b]
    linear_combination -(c W.a₁) ^ 3 * hc
  exact isUnit_of_mul_isUnit_left (hid ▸ hu)

end FLT.Mazur.WeierstrassIntegralChart
