/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicCompletionRegular
public import FLT.PadicHodgeTheory.AdicPrincipalDVR
public import FLT.PadicHodgeTheory.ComplexDeRhamResidue
public import Mathlib.RingTheory.WittVector.Domain

/-! # The actual B_dR^+ is a discrete valuation ring -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The prime is nonzero in A_inf because its theta image is nonzero. -/
theorem complexAinf_prime_ne_zero : (p : Ainf p) ≠ 0 := by
  intro h
  have he := congrArg (complexTheta p) h
  simp only [map_natCast, map_zero] at he
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) he

/-- Inverting the nonzero prime in the actual Witt domain preserves the domain. -/
instance instIsDomainComplexAinfInvertP : IsDomain (ComplexAinfInvertP p) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (complexAinf_prime_ne_zero p))

/-- The constructed integral theta generator is nonzero. -/
theorem complexThetaGenerator_ne_zero : complexThetaGenerator p ≠ 0 := by
  intro h
  have he := congrArg (fun x : Ainf p ↦ x.coeff 0) h
  rw [complexThetaGenerator_coeff_zero, WittVector.zero_coeff] at he
  apply complexPrimeTilt_sharp_ne_zero p
  rw [he]
  exact Perfection.teichmuller_zero

/-- Its image after inverting p remains nonzero. -/
theorem complexThetaGenerator_localized_ne_zero :
    algebraMap (Ainf p) (ComplexAinfInvertP p) (complexThetaGenerator p) ≠ 0 := by
  apply (map_ne_zero_iff _ (IsLocalization.injective (ComplexAinfInvertP p)
    (powers_le_nonZeroDivisors_of_noZeroDivisors (complexAinf_prime_ne_zero p)))).mpr
  exact complexThetaGenerator_ne_zero p

/-- The parameter remains a non-zero-divisor after the actual theta-adic completion. -/
theorem complexDeRhamParameter_regular (x : ComplexBDeRhamPlus p)
    (hx : complexDeRhamParameter p * x = 0) : x = 0 := by
  exact adicCompletion_parameter_mul_eq_zero_of_span
    (ComplexDeRhamIdeal p) _ (complexThetaInvertP_ker_eq_span p)
    (complexThetaGenerator_localized_ne_zero p) x hx

/-- The completed local ring is a domain, derived from regularity and separatedness. -/
instance instIsDomainComplexDeRham : IsDomain (ComplexBDeRhamPlus p) :=
  adicParameter_isDomain (complexDeRhamParameter p) (complexDeRham_maximalIdeal p)
    (complexDeRhamParameter_regular p)

/-- The completed parameter is nonzero. -/
theorem complexDeRhamParameter_ne_zero : complexDeRhamParameter p ≠ 0 := by
  intro h
  have he := complexDeRhamParameter_regular p 1 (by rw [h, zero_mul])
  exact one_ne_zero he

/-- The actual de Rham period ring B_dR^+ is a discrete valuation ring. -/
instance instIsDiscreteValuationRingComplexDeRham :
    IsDiscreteValuationRing (ComplexBDeRhamPlus p) :=
  adicParameter_isDiscreteValuationRing (complexDeRhamParameter p)
    (complexDeRham_maximalIdeal p) (complexDeRhamParameter_ne_zero p)

/-- The image of the actual theta generator is a uniformizer. -/
theorem complexDeRhamParameter_irreducible : Irreducible (complexDeRhamParameter p) :=
  IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _
    (complexDeRhamParameter_ne_zero p) (complexDeRham_maximalIdeal p)

end PadicHodgeTheory
