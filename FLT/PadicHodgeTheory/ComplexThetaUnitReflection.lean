/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicUnitReflection
public import FLT.PadicHodgeTheory.ComplexTiltDivisibility

/-! # Unit detection through sharp, theta and Frobenius -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- A unit sharp value detects a unit in the actual integral tilt. -/
theorem complexTilt_isUnit_of_sharp (x : IntegralTilt p)
    (hx : IsUnit (complexSharp p x)) : IsUnit x := by
  apply isUnit_iff_dvd_one.mpr
  apply complexTilt_dvd_of_sharp_dvd p x 1 hx.ne_zero
  simpa only [map_one] using (hx.dvd : complexSharp p x ∣ (1 : 𝓞_ℂ_[p]))

/-- Unit reduction at the zeroth tilt coordinate detects a unit. -/
theorem complexTilt_isUnit_of_coeff (x : IntegralTilt p)
    (hx : IsUnit (PreTilt.coeff 0 x)) : IsUnit x := by
  apply complexTilt_isUnit_of_sharp
  apply isUnit_of_adic_quotient (Ideal.span {(p : 𝓞_ℂ_[p])})
  rwa [complexSharp_modP]

/-- Unit reduction at the zeroth Witt coordinate detects a unit in A_inf. -/
theorem complexWitt_isUnit_of_coeff (x : Ainf p) (hx : IsUnit (x.coeff 0)) : IsUnit x := by
  apply isUnit_of_adic_image (Ideal.span {(p : Ainf p)}) WittVector.constantCoeff
    (WittVector.constantCoeff_surjective p) _ x hx
  intro y hy
  exact (WittVector.mem_span_p_iff_coeff_zero_eq_zero y).mpr hy

/-- The lift of Frobenius on the coefficient ring to the actual Witt ring. -/
def complexWittFrobenius : Ainf p →+* Ainf p :=
  WittVector.map (frobenius (IntegralTilt p) p)

/-- Theta after Frobenius detects units, using both genuine adic completions. -/
theorem complexWitt_isUnit_of_theta_frobenius (x : Ainf p)
    (hx : IsUnit (complexTheta p (complexWittFrobenius p x))) : IsUnit x := by
  apply complexWitt_isUnit_of_coeff
  apply complexTilt_isUnit_of_coeff
  have h := hx.map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞_ℂ_[p])}))
  rw [complexTheta_modP] at h
  change IsUnit (PreTilt.coeff 0 ((x.coeff 0) ^ p)) at h
  rw [map_pow] at h
  exact (isUnit_pow_iff (Fact.out : p.Prime).ne_zero).mp h

/-- Frobenius acts on Teichmuller representatives by taking pth powers. -/
theorem complexWittFrobenius_teichmuller (x : IntegralTilt p) :
    complexWittFrobenius p (WittVector.teichmuller p x) = WittVector.teichmuller p (x ^ p) :=
  WittVector.map_teichmuller p _ _

end PadicHodgeTheory
