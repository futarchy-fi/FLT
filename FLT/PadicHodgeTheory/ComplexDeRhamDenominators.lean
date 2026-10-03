/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamDVR

/-! # The actual denominators in Mathlib's de Rham localization -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The denominator monoid in the existing definition of B_dR. -/
def complexDeRhamDenominators : Submonoid (ComplexBDeRhamPlus p) :=
  Submonoid.closure <| algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p) ''
    {a | ComplexDeRhamIdeal p = Ideal.span {a}}

/-- Every source theta generator becomes an associate of the actual completed parameter. -/
theorem complexDeRhamGenerator_associated {a : ComplexAinfInvertP p}
    (ha : ComplexDeRhamIdeal p = Ideal.span {a}) :
    Associated (complexDeRhamParameter p)
      (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p) a) := by
  have h := Ideal.span_singleton_eq_span_singleton.mp
    ((complexThetaInvertP_ker_eq_span p).symm.trans ha)
  exact h.map (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p))

/-- The denominator set is nonempty: it contains the constructed completed parameter. -/
theorem complexDeRhamParameter_mem_denominators :
    complexDeRhamParameter p ∈ complexDeRhamDenominators p := by
  apply Submonoid.subset_closure
  exact ⟨algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p),
    complexThetaInvertP_ker_eq_span p, rfl⟩

/-- None of the actual denominators is zero or a zero divisor. -/
theorem complexDeRhamDenominators_le :
    complexDeRhamDenominators p ≤ nonZeroDivisors (ComplexBDeRhamPlus p) := by
  apply Submonoid.closure_le.mpr
  rintro x ⟨a, ha, rfl⟩
  apply mem_nonZeroDivisors_iff_ne_zero.mpr
  exact (complexDeRhamGenerator_associated p ha).ne_zero_iff.mp
    (complexDeRhamParameter_ne_zero p)

/-- Expose the ring structure of the actual localization. -/
instance instCommRingComplexBDeRham : CommRing (ComplexBDeRham p) :=
  inferInstanceAs (CommRing (Localization (complexDeRhamDenominators p)))

/-- The existing B_dR is naturally an algebra over the existing B_dR^+. -/
instance instAlgebraComplexBDeRham : Algebra (ComplexBDeRhamPlus p) (ComplexBDeRham p) :=
  inferInstanceAs (Algebra (ComplexBDeRhamPlus p) (Localization (complexDeRhamDenominators p)))

/-- It has precisely the localization property of its defining denominator monoid. -/
instance instIsLocalizationComplexBDeRham :
    IsLocalization (complexDeRhamDenominators p) (ComplexBDeRham p) :=
  inferInstanceAs (IsLocalization (complexDeRhamDenominators p)
    (Localization (complexDeRhamDenominators p)))

end PadicHodgeTheory
