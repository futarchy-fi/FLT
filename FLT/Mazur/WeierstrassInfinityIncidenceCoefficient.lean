/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartCoefficientRingMap
public import FLT.Mazur.WeierstrassInfinityNilpotentIncidence

/-!
# The full regular infinity incidence commutes with coefficient changes

The complete cubic denominator, including its nilpotent corrections, follows
the original coefficient map. Cancellation of that unit proves naturality of
the regular incidence without choosing compatible inverse constructions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R)

/-- The full original cubic denominator follows every coefficient homomorphism. -/
theorem chartCoefficientRingMap_denominator :
    chartCoefficientRingMap f W 1 (nilpotentInfinityDenominator W) =
      nilpotentInfinityDenominator (W.map f) := by
  simp only [nilpotentInfinityDenominator, map_sub, map_add, map_mul, map_pow, map_one,
    chartCoefficientRingMap_scalar, chartCoefficientRingMap_coord,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆]

variable (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)

/-- The regular incidence retains its exact full cubic denominator equation. -/
theorem nilpotentInfinityIncidence_denominator (s : R) :
    nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s * nilpotentInfinityDenominator W =
      algebraMap R (Coordinate W 1) s * coord W 1 0 ^ 2 := by
  rw [nilpotentInfinityIncidence, mul_assoc,
    (nilpotentInfinityDenominator_isUnit W I hI h2 h3 h4 h6).val_inv_mul, mul_one]

variable (J : Ideal S) (hf : I ≤ J.comap f) (hJ : IsNilpotent J)

/-- The full regular incidence is natural on the entire original infinity chart. -/
theorem chartCoefficientRingMap_incidence (s : R) :
    chartCoefficientRingMap f W 1 (nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s) =
      nilpotentInfinityIncidence (W.map f) J hJ (hf h2) (hf h3) (hf h4) (hf h6) (f s) := by
  apply (nilpotentInfinityDenominator_isUnit (W.map f) J hJ
    (hf h2) (hf h3) (hf h4) (hf h6)).mul_right_cancel
  rw [nilpotentInfinityIncidence_denominator, ← chartCoefficientRingMap_denominator f W,
    ← map_mul, nilpotentInfinityIncidence_denominator, map_mul, map_pow,
    chartCoefficientRingMap_scalar, chartCoefficientRingMap_coord]

end FLT.Mazur.WeierstrassIntegralChart
