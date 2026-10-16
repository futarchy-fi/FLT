/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNilpotentDenominator

/-!
# The original incidence coordinate extends across arithmetic infinity

The exact full cubic denominator constructs s/x without inverting X/Y. Its
product with X/Y is s times Z/Y on the entire original infinity chart.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
local notation "B" => Coordinate W 1
local notation "u" => coord W 1 0
local notation "w" => coord W 1 2
local notation "c" => algebraMap R B
local notation "hd" => nilpotentInfinityDenominator_isUnit W I hI h2 h3 h4 h6
local notation "d" => IsUnit.unit hd

/-- The exact unit denominator of the full original cubic on the infinity chart. -/
def nilpotentInfinityDenominatorUnit : Bˣ := d

/-- The unit retains the full original cubic denominator. -/
theorem nilpotentInfinityDenominatorUnit_val :
    (nilpotentInfinityDenominatorUnit W I hI h2 h3 h4 h6 : B) =
      nilpotentInfinityDenominator W := (hd).unit_spec

/-- The original s/x coordinate is regular on the complete infinity chart. -/
def nilpotentInfinityIncidence (s : R) : B := c s * u ^ 2 * (↑d⁻¹ : B)

/-- The regular extension satisfies the exact original projective incidence equation. -/
theorem nilpotentInfinityIncidence_mul (s : R) :
    nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s * u = c s * w := by
  apply (hd).mul_right_cancel
  change (c s * u ^ 2 * (↑d⁻¹ : B) * u) * nilpotentInfinityDenominator W = _
  calc
    _ = c s * u ^ 3 * ((↑d⁻¹ : B) * nilpotentInfinityDenominator W) := by ring
    _ = c s * u ^ 3 := by rw [(hd).val_inv_mul, mul_one]
    _ = c s * w * nilpotentInfinityDenominator W := by
      rw [← nilpotentInfinityDenominator_cubic W, mul_assoc]

/-- The original arithmetic ideal also contains the extended incidence coordinate. -/
theorem nilpotentInfinityIncidence_mem (s : R) (hs : s ∈ I) :
    nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s ∈ I.map c :=
  (I.map c).mul_mem_right _ ((I.map c).mul_mem_right _ (Ideal.mem_map_of_mem c hs))

end FLT.Mazur.WeierstrassIntegralChart
