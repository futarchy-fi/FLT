/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexSharpSurjective
public import FLT.PadicHodgeTheory.ComplexTiltDivisibility

/-! # An actual candidate generator of the Fontaine theta kernel -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- Choose compatible p-power roots of p in the actual integral tilt. -/
def complexPrimeTilt : IntegralTilt p := (complexSharp_surjective p (p : 𝓞_ℂ_[p])).choose

/-- The chosen tilt element has sharp equal to p. -/
@[simp] theorem complexPrimeTilt_sharp : complexSharp p (complexPrimeTilt p) = p :=
  (complexSharp_surjective p (p : 𝓞_ℂ_[p])).choose_spec

/-- The sharp of the chosen element is nonzero. -/
theorem complexPrimeTilt_sharp_ne_zero : complexSharp p (complexPrimeTilt p) ≠ 0 := by
  rw [complexPrimeTilt_sharp]
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- The element [p-flat] - p in the actual A_inf. -/
def complexThetaGenerator : Ainf p := WittVector.teichmuller p (complexPrimeTilt p) - p

/-- The candidate belongs to the actual theta kernel. -/
theorem complexThetaGenerator_mem_ker :
    complexThetaGenerator p ∈ RingHom.ker (complexTheta p) := by
  change complexTheta p (complexThetaGenerator p) = 0
  simp only [complexThetaGenerator, map_sub, complexTheta_teichmuller,
    complexPrimeTilt_sharp, map_natCast, sub_self]

/-- Modulo p, the candidate is exactly the chosen prime element of the tilt. -/
theorem complexThetaGenerator_coeff_zero :
    (complexThetaGenerator p).coeff 0 = complexPrimeTilt p := by
  change WittVector.constantCoeff (complexThetaGenerator p) = _
  simp only [complexThetaGenerator, map_sub, map_natCast, CharP.cast_eq_zero,
    sub_zero]
  rfl

/-- Every element killed by the zeroth tilt coordinate is divisible by p-flat. -/
theorem complexPrimeTilt_dvd_of_coeff_zero (x : IntegralTilt p)
    (hx : PreTilt.coeff 0 x = 0) : complexPrimeTilt p ∣ x := by
  apply complexTilt_dvd_of_sharp_dvd p _ _ (complexPrimeTilt_sharp_ne_zero p)
  rw [complexPrimeTilt_sharp, ← Ideal.mem_span_singleton,
    ← Ideal.Quotient.eq_zero_iff_mem]
  exact (complexSharp_modP p x).trans hx

/-- The Witt reduction of every actual theta-kernel element is divisible by p-flat. -/
theorem complexTheta_ker_coeff_dvd (x : Ainf p) (hx : x ∈ RingHom.ker (complexTheta p)) :
    complexPrimeTilt p ∣ x.coeff 0 := by
  apply complexPrimeTilt_dvd_of_coeff_zero
  rw [← complexTheta_modP, show complexTheta p x = 0 from hx, map_zero]

end PadicHodgeTheory
