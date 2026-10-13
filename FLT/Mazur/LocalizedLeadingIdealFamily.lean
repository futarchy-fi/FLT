/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLeadingIdealFamily
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Leading families survive injective coefficient localization

Every equation in the extended ideal is one original equation divided by a
coefficient denominator. Injectivity preserves its leading monomial, so the
original finite family still controls all equations after localization.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace FLT.Mazur.LocalizedLeadingIdealFamily
variable {σ R S : Type*} [CommRing R] [CommRing S] (m : MonomialOrder σ)

/-- An injective coefficient map preserves the complete leading exponent. -/
theorem degree_map (φ : R →+* S) (hφ : Function.Injective φ) (p : MvPolynomial σ R) :
    m.degree (map φ p) = m.degree p := by
  classical
  simp only [MonomialOrder.degree, support_map_of_injective p hφ]

/-- The leading coefficient is the image of the original coefficient. -/
theorem leadingCoeff_map (φ : R →+* S) (hφ : Function.Injective φ)
    (p : MvPolynomial σ R) : m.leadingCoeff (map φ p) = φ (m.leadingCoeff p) := by
  rw [MonomialOrder.leadingCoeff, degree_map m φ hφ, coeff_map]
  rfl

variable [Algebra R S] (M : Submonoid R) [IsLocalization M S]
  (hφ : Function.Injective (algebraMap R S))
  (I : Ideal (MvPolynomial σ R))
attribute [local instance] MvPolynomial.algebraMvPolynomial
include M hφ

/-- A nonzero localized ideal equation has an original numerator with the same leading exponent. -/
theorem exists_numerator (q : MvPolynomial σ S)
    (hq : q ∈ I.map (map (algebraMap R S))) (hq0 : q ≠ 0) :
    ∃ p ∈ I, p ≠ 0 ∧ m.degree p = m.degree q := by
  obtain ⟨⟨p, t⟩, ht⟩ :=
    (IsLocalization.mem_map_algebraMap_iff (M.map (C (σ := σ)))
      (MvPolynomial σ S)).mp hq
  obtain ⟨r, hr, her⟩ := t.property
  have he : (algebraMap R S r) • q = map (algebraMap R S) p.val := by
    rw [smul_eq_C_mul, mul_comm]
    simpa only [← her, MvPolynomial.algebraMap_def, map_C] using ht
  have hu : IsUnit (algebraMap R S r) := IsLocalization.map_units S ⟨r, hr⟩
  refine ⟨p.val, p.property, ?_, ?_⟩
  · intro hp0
    rw [hp0, map_zero] at he
    exact hq0 (hu.smul_eq_zero.mp he)
  · rw [← degree_map m (algebraMap R S) hφ, ← he]
    exact m.degree_smul_of_isRegular hu.isRegular

variable [Finite σ]

/-- The images of the selected original equations control the entire extended ideal. -/
theorem family_covers (q : MvPolynomial σ S)
    (hq : q ∈ I.map (map (algebraMap R S))) (hq0 : q ≠ 0) :
    ∃ b ∈ FiniteLeadingIdealFamily.family m I,
      m.degree (map (algebraMap R S) b) ≤ m.degree q := by
  obtain ⟨p, hp, hp0, hpq⟩ := exists_numerator m M hφ I q hq hq0
  obtain ⟨b, hb, hbp⟩ := FiniteLeadingIdealFamily.family_covers m I p hp hp0
  refine ⟨b, hb, ?_⟩
  rwa [degree_map m (algebraMap R S) hφ, ← hpq]

end FLT.Mazur.LocalizedLeadingIdealFamily
