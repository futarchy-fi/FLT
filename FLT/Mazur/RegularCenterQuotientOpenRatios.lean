/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterRatioCover

/-!
# Original ratios on the actual quotient opens

The quotient-open lift divides original numerators by the chosen generator
quotient. These identities remain valid on the exceptional fiber, where the
original denominator vanishes and therefore cannot be cancelled.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.RegularCenter
open BlowupFractionChart
set_option backward.isDefEq.respectTransparency false
variable {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (a : A) (ha : a ∈ I) (hd : IsRegular d)

include hd in
/-- The retained input denominator stays regular on every actual quotient open. -/
theorem quotientOpen_input_regular :
    IsRegular (algebraMap B (QuotientOpen I φ d hI a ha) d) := by
  apply isRegular_iff_mem_nonZeroDivisors.mpr
  exact IsLocalization.nonZeroDivisors_le_comap
    (M := Submonoid.powers (quotient I φ d hI a ha))
    (S := QuotientOpen I φ d hI a ha)
    (isRegular_iff_mem_nonZeroDivisors.mp hd)

/-- Actual fraction ratios are quotients of the original center quotients. -/
theorem quotient_mul_quotientOpenLift_ratio (b : A) (hb : b ∈ I) :
    algebraMap B (QuotientOpen I φ d hI a ha) (quotient I φ d hI a ha) *
        quotientOpenLift I φ d hI a ha hd (ratio I a b hb) =
      algebraMap B _ (quotient I φ d hI b hb) := by
  apply (quotientOpen_input_regular I φ d hI a ha hd).left
  dsimp only
  rw [← mul_assoc, ← map_mul, denominator_mul_quotient,
    ← map_mul, denominator_mul_quotient, quotientOpenLift_def]
  exact principalLift_ratio I (onQuotientOpen I φ d hI a ha) a _ _ b hb

/-- The same ratio formula survives arbitrary restriction of the quotient open. -/
theorem quotientOpenLift_ratio_specialize
    (ψ : QuotientOpen I φ d hI a ha →+* C) (b : A) (hb : b ∈ I) :
    ψ (algebraMap B _ (quotient I φ d hI a ha)) *
        ψ (quotientOpenLift I φ d hI a ha hd (ratio I a b hb)) =
      ψ (algebraMap B _ (quotient I φ d hI b hb)) := by
  rw [← map_mul, quotient_mul_quotientOpenLift_ratio]

/-- The multiplier in the residue ratio identity is still a unit, even on the exceptional fiber. -/
theorem quotientOpen_generator_specialize_isUnit
    (ψ : QuotientOpen I φ d hI a ha →+* C) :
    IsUnit (ψ (algebraMap B _ (quotient I φ d hI a ha))) :=
  (IsLocalization.Away.algebraMap_isUnit (quotient I φ d hI a ha)).map ψ

end FLT.Mazur.RegularCenter
