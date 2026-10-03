/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexThetaLocalized
public import FLT.PadicHodgeTheory.ComplexThetaQuotientInvertP

/-! # The coefficient quotients are the actual finite levels of the de Rham completion -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The finite levels in the existing definition of B_dR+. -/
abbrev ComplexFiniteThetaQuotient (n : ℕ) :=
  ComplexAinfInvertP p ⧸ RingHom.ker (complexThetaInvertP p) ^ n

/-- Reduction modulo the integral theta power carries p-powers to p-powers. -/
theorem complexThetaQuotient_mk_map_powers (n : ℕ) :
    (Submonoid.powers (p : Ainf p)).map
      (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n)) =
        Submonoid.powers (p : ComplexIntegralThetaQuotient p n) := by
  rw [Submonoid.map_powers, map_natCast]

/-- Localize the actual quotient map of A_inf. -/
def complexThetaQuotientLocalizationMap (n : ℕ) :
    ComplexAinfInvertP p →+* ComplexThetaQuotientInvertP p n :=
  IsLocalization.map _ (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n))
    ((complexThetaQuotient_mk_map_powers p n).symm ▸
      (Submonoid.powers (p : Ainf p)).le_comap_map)

/-- The localized map agrees with the original integral quotient map. -/
@[simp] theorem complexThetaQuotientLocalizationMap_algebraMap (n : ℕ) (a : Ainf p) :
    complexThetaQuotientLocalizationMap p n (algebraMap (Ainf p) (ComplexAinfInvertP p) a) =
      algebraMap (ComplexIntegralThetaQuotient p n) (ComplexThetaQuotientInvertP p n)
        (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n) a) :=
  IsLocalization.map_eq _ _

/-- Surjectivity of the finite-level reduction persists after inverting p. -/
theorem complexThetaQuotientLocalizationMap_surjective (n : ℕ) :
    Function.Surjective (complexThetaQuotientLocalizationMap p n) := by
  let : IsLocalization ((Submonoid.powers (p : Ainf p)).map
      (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n)))
      (ComplexThetaQuotientInvertP p n) := by
    rw [complexThetaQuotient_mk_map_powers]
    infer_instance
  exact IsLocalization.map_surjective_of_surjective _ _ _ Ideal.Quotient.mk_surjective

/-- The localized reduction kernel is exactly the actual localized theta-kernel power. -/
theorem complexThetaQuotientLocalizationMap_ker (n : ℕ) :
    RingHom.ker (complexThetaQuotientLocalizationMap p n) =
      RingHom.ker (complexThetaInvertP p) ^ n := by
  rw [complexThetaQuotientLocalizationMap, IsLocalization.ker_map _ _
    (complexThetaQuotient_mk_map_powers p n), Ideal.mk_ker, Ideal.map_pow,
    complexTheta_ker_eq_span, Ideal.map_span, Set.image_singleton,
    complexThetaInvertP_ker_eq_span]

/-- The actual finite theta level equals the p-inversion of the integral theta quotient. -/
def complexFiniteThetaQuotientEquiv (n : ℕ) :
    ComplexFiniteThetaQuotient p n ≃+* ComplexThetaQuotientInvertP p n :=
  (Ideal.quotEquivOfEq (complexThetaQuotientLocalizationMap_ker p n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (complexThetaQuotientLocalizationMap_surjective p n))

/-- The identification is the canonical localized quotient map on representatives. -/
@[simp] theorem complexFiniteThetaQuotientEquiv_mk (n : ℕ) (a : ComplexAinfInvertP p) :
    complexFiniteThetaQuotientEquiv p n
      (Ideal.Quotient.mk (RingHom.ker (complexThetaInvertP p) ^ n) a) =
        complexThetaQuotientLocalizationMap p n a := rfl

end PadicHodgeTheory
