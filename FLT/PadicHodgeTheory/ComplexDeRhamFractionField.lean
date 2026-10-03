/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamDenominators
public import FLT.PadicHodgeTheory.ComplexCyclotomicLogOrder
public import FLT.PadicHodgeTheory.DiscreteValuationLocalization

/-! # The actual B_dR is the fraction field and is obtained by inverting t -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Mathlib's actual de Rham localization is the fraction ring of the actual DVR. -/
instance instIsFractionRingComplexBDeRham :
    IsFractionRing (ComplexBDeRhamPlus p) (ComplexBDeRham p) :=
  discreteValuation_isFractionRing (complexDeRhamDenominators_le p)
    (complexDeRhamParameter_irreducible p) (complexDeRhamParameter_mem_denominators p)

/-- The existing B_dR is a field, rather than merely a localization at a formal set. -/
noncomputable instance instFieldComplexBDeRham : Field (ComplexBDeRham p) :=
  IsFractionRing.toField (ComplexBDeRhamPlus p)

/-- The inclusion of the constructed B_dR^+ into B_dR is injective. -/
theorem complexDeRhamToField_injective :
    Function.Injective (algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p)) :=
  IsFractionRing.injective _ _

/-- Inverting the constructed logarithmic period also gives the same fraction field. -/
instance instIsFractionRingComplexLogLocalization :
    IsFractionRing (ComplexBDeRhamPlus p) (Localization.Away (complexCyclotomicLog p)) :=
  discreteValuation_away_isFractionRing (complexCyclotomicLog_irreducible p)

/-- Canonical algebraic identification of the existing B_dR with B_dR^+[1/t]. -/
def complexDeRhamLogLocalizationEquiv :
    ComplexBDeRham p ≃ₐ[ComplexBDeRhamPlus p] Localization.Away (complexCyclotomicLog p) :=
  IsLocalization.algEquiv (nonZeroDivisors (ComplexBDeRhamPlus p)) _ _

/-- The period is nonzero in the actual period field. -/
theorem complexCyclotomicLog_field_ne_zero :
    algebraMap (ComplexBDeRhamPlus p) (ComplexBDeRham p) (complexCyclotomicLog p) ≠ 0 :=
  (map_ne_zero_iff _ (complexDeRhamToField_injective p)).mpr (complexCyclotomicLog_ne_zero p)

end PadicHodgeTheory
