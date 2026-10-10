/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesDegreeZeroMap

/-!
# Degree-zero Rees localizations are the actual fraction charts

A homogeneous fraction can vanish only when a power of the original chart
denominator kills its coefficient. The same power of f*T kills its numerator
in the Rees algebra. Thus evaluation is injective even over rings with zero divisors.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type*} [CommRing A] (I : Ideal A) (f : A) (hf : f ∈ I)

/-- A power of the degree-one generator is the corresponding original monomial. -/
theorem generator_pow_coe (n : ℕ) :
    ((generator I f hf ^ n : reesAlgebra I) : A[X]) = Polynomial.monomial n (f ^ n) := by
  change (Polynomial.monomial 1 f) ^ n = _
  rw [Polynomial.monomial_pow, one_mul]

/-- A homogeneous fraction vanishes if its original numerator vanishes after inverting f. -/
theorem homogeneousFraction_eq_zero (n : ℕ) (a : ↥(I ^ n))
    (ha : algebraMap A (Localization.Away f) (a : A) = 0) :
    homogeneousFraction I f hf n a = 0 := by
  obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
    (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) (a : A)).mp ha
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, homogeneousFraction,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
  apply (IsLocalization.mk'_eq_zero_iff _ _).mpr
  refine ⟨⟨generator I f hf ^ m, m, rfl⟩, ?_⟩
  apply Subtype.ext
  change ((generator I f hf ^ m : reesAlgebra I) : A[X]) * Polynomial.monomial n (a : A) = 0
  rw [generator_pow_coe, Polynomial.monomial_mul_monomial, hm, map_zero]

/-- The actual degree-zero localization embeds in the original fraction chart. -/
theorem degreeZeroToFraction_injective : Function.Injective (degreeZeroToFraction I f hf) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (component I)
    (generator_mem I f hf) z
  have hp' : p ∈ component I n := by simpa only [smul_eq_mul, mul_one] using hp
  obtain ⟨a, rfl⟩ := hp'
  change degreeZeroToFraction I f hf (homogeneousFraction I f hf n a) = 0 at hz
  have hc := congrArg (fun q : BlowupFractionChart.chart I f => (q : Localization.Away f)) hz
  rw [degreeZeroToFraction_coe, ZeroMemClass.coe_zero] at hc
  have ha : algebraMap A (Localization.Away f) (a : A) = 0 := by
    have h := congrArg (fun q : Localization.Away f => q * algebraMap A _ f ^ n) hc
    rw [mul_assoc, ← mul_pow, mul_comm (IsLocalization.Away.invSelf f),
      IsLocalization.Away.mul_invSelf, one_pow, mul_one, zero_mul] at h
    exact h
  exact homogeneousFraction_eq_zero I f hf n a ha

/-- The original degree-zero Rees chart is the actual fraction algebra A[I/f]. -/
def degreeZeroEquiv : DegreeZeroChart I f hf ≃+* BlowupFractionChart.chart I f :=
  RingEquiv.ofBijective (degreeZeroToFraction I f hf)
    ⟨degreeZeroToFraction_injective I f hf, degreeZeroToFraction_surjective I f hf⟩

/-- The comparison retains every original homogeneous fraction. -/
theorem degreeZeroEquiv_fraction (n : ℕ) (a : ↥(I ^ n)) :
    (degreeZeroEquiv I f hf (homogeneousFraction I f hf n a) : Localization.Away f) =
      algebraMap A (Localization.Away f) a * IsLocalization.Away.invSelf f ^ n :=
  degreeZeroToFraction_coe I f hf n a

end FLT.Mazur.BlowupRees
