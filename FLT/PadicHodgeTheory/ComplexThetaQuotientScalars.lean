/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexPadicScalars
public import FLT.PadicHodgeTheory.ComplexThetaQuotientInvertP
public import FLT.PadicHodgeTheory.PadicScalarTopology

/-! # Continuous actual p-adic scalar maps into the finite theta quotients -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual integral scalar map reduced modulo the n-th theta-kernel power. -/
def complexIntegralThetaQuotientScalars (n : ℕ) : ℤ_[p] →+* ComplexIntegralThetaQuotient p n :=
  (Ideal.Quotient.mk (RingHom.ker (complexTheta p) ^ n)).comp (complexPadicIntToAinf p)

/-- The integral scalar map is continuous for the standard topology on Z_p. -/
theorem complexIntegralThetaQuotientScalars_continuous (n : ℕ) :
    Continuous (complexIntegralThetaQuotientScalars p n) :=
  padicInt_hom_continuous p rfl _

/-- Integral scalars in the p-inverted finite quotient. -/
def complexThetaQuotientInvertPIntScalars (n : ℕ) : ℤ_[p] →+* ComplexThetaQuotientInvertP p n :=
  (algebraMap _ _).comp (complexIntegralThetaQuotientScalars p n)

/-- Every nonzero integral scalar becomes a unit after inverting p. -/
theorem complexThetaQuotientInvertPIntScalars_isUnit (n : ℕ) (x : ℤ_[p]) (hx : x ≠ 0) :
    IsUnit (complexThetaQuotientInvertPIntScalars p n x) := by
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx
    (PadicInt.irreducible_p (p := p))
  apply (hk.map (complexThetaQuotientInvertPIntScalars p n)).isUnit_iff.mpr
  have hp := IsLocalization.Away.algebraMap_isUnit
    (S := ComplexThetaQuotientInvertP p n) (p : ComplexIntegralThetaQuotient p n)
  simpa only [map_pow, map_natCast] using hp.pow k

/-- The actual Q_p scalar map, extended through the fraction-ring universal property. -/
def complexThetaQuotientInvertPScalars (n : ℕ) : ℚ_[p] →+* ComplexThetaQuotientInvertP p n :=
  IsLocalization.lift (M := nonZeroDivisors ℤ_[p])
    (g := complexThetaQuotientInvertPIntScalars p n)
    (fun x ↦ complexThetaQuotientInvertPIntScalars_isUnit p n x
      (nonZeroDivisors.ne_zero x.property))

/-- Compatibility of the rational scalar map with its integral construction. -/
theorem complexThetaQuotientInvertPScalars_int (n : ℕ) (x : ℤ_[p]) :
    complexThetaQuotientInvertPScalars p n (algebraMap ℤ_[p] ℚ_[p] x) =
      complexThetaQuotientInvertPIntScalars p n x := IsLocalization.lift_eq _ _

/-- The integral scalar map into the localization is continuous. -/
theorem complexThetaQuotientInvertPIntScalars_continuous (n : ℕ) :
    Continuous (complexThetaQuotientInvertPIntScalars p n) :=
  (complexThetaQuotientInvertP_continuous p n).comp
    (complexIntegralThetaQuotientScalars_continuous p n)

/-- The Q_p map is continuous for the standard p-adic topology, by the open integral inclusion. -/
theorem complexThetaQuotientInvertPScalars_continuous (n : ℕ) :
    Continuous (complexThetaQuotientInvertPScalars p n) := by
  apply continuous_of_continuousAt_zero (complexThetaQuotientInvertPScalars p n)
  have h : ContinuousAt
      (complexThetaQuotientInvertPScalars p n ∘ ((↑) : ℤ_[p] → ℚ_[p])) (0 : ℤ_[p]) := by
    have he : complexThetaQuotientInvertPScalars p n ∘ ((↑) : ℤ_[p] → ℚ_[p]) =
        complexThetaQuotientInvertPIntScalars p n :=
      funext fun x ↦ complexThetaQuotientInvertPScalars_int p n x
    rw [he]
    exact (complexThetaQuotientInvertPIntScalars_continuous p n).continuousAt
  exact (PadicInt.isOpenEmbedding_coe (p := p)).continuousAt_iff.mp h

/-- The integral scalar maps commute with transitions. -/
@[simp] theorem complexIntegralThetaQuotient_transition_scalars {m n : ℕ} (h : n ≤ m)
    (x : ℤ_[p]) :
    Ideal.Quotient.factorPow (RingHom.ker (complexTheta p)) h
      (complexIntegralThetaQuotientScalars p m x) = complexIntegralThetaQuotientScalars p n x :=
  rfl

/-- The rational scalar maps commute with the localized transitions. -/
theorem complexThetaQuotientInvertPTransition_scalars {m n : ℕ} (h : n ≤ m) (x : ℚ_[p]) :
    complexThetaQuotientInvertPTransition p h (complexThetaQuotientInvertPScalars p m x) =
      complexThetaQuotientInvertPScalars p n x := by
  have he : (complexThetaQuotientInvertPTransition p h).comp
      (complexThetaQuotientInvertPScalars p m) = complexThetaQuotientInvertPScalars p n := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    ext a
    simp only [RingHom.comp_apply, complexThetaQuotientInvertPScalars_int,
      complexThetaQuotientInvertPIntScalars, complexThetaQuotientInvertPTransition_algebraMap,
      complexIntegralThetaQuotient_transition_scalars]
  exact RingHom.congr_fun he x

end PadicHodgeTheory
