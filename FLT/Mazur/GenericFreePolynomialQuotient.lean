/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedLeadingIdealFamily
public import FLT.Mazur.MonicIdealNormalForms

/-!
# Generic freeness of polynomial quotients

For any ideal in finitely many variables over a domain, invert the constructed
nonzero product of leading coefficients. The actual extended ideal quotient
then has a basis of standard monomials. No finite generation of the ideal and
no pre-existing flatness assumption are required.
-/

@[expose] public noncomputable section
open MvPolynomial
namespace FLT.Mazur.GenericFreePolynomialQuotient
open FiniteLeadingIdealFamily
variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R]
  (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ R))
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away (denominator m I) S]
include m I

/-- The explicit denominator is nonzero, so the localization keeps all coefficients distinct. -/
theorem coefficient_injective : Function.Injective (algebraMap R S) :=
  IsLocalization.injective S
    (powers_le_nonZeroDivisors_of_noZeroDivisors (denominator_ne_zero m I))

/-- The original quotient becomes free over this explicit coefficient localization. -/
theorem quotient_free :
    Module.Free S (MvPolynomial σ S ⧸ I.map (map (algebraMap R S))) := by
  let s : Set (MvPolynomial σ S) := map (algebraMap R S) '' (family m I : Set _)
  have hi := coefficient_injective m I S
  apply MonicIdealNormalForms.quotient_free m _ s
  · rintro _ ⟨b, hb, rfl⟩
    exact Ideal.mem_map_of_mem _ (family_mem m I b hb)
  · rintro _ ⟨b, hb, rfl⟩
    rw [LocalizedLeadingIdealFamily.leadingCoeff_map m _ hi]
    exact leadingCoeff_isUnit m I (algebraMap R S)
      (IsLocalization.Away.algebraMap_isUnit (denominator m I)) b hb
  · intro q hq hq0
    obtain ⟨b, hb, hbp⟩ := LocalizedLeadingIdealFamily.family_covers m
      (Submonoid.powers (denominator m I)) hi I q hq hq0
    exact ⟨map (algebraMap R S) b, ⟨b, hb, rfl⟩, hbp⟩

/-- In particular the localized polynomial quotient is flat. -/
theorem quotient_flat :
    Module.Flat S (MvPolynomial σ S ⧸ I.map (map (algebraMap R S))) := by
  let _ := quotient_free m I S
  exact Module.Flat.of_free

/-- A concrete nonzero coefficient suffices, without assuming a generic-flatness theorem. -/
theorem exists_free_localization : ∃ r : R, r ≠ 0 ∧
    Module.Free (Localization.Away r)
      (MvPolynomial σ (Localization.Away r) ⧸
        I.map (map (algebraMap R (Localization.Away r)))) :=
  ⟨denominator m I, denominator_ne_zero m I,
    quotient_free m I (Localization.Away (denominator m I))⟩

end FLT.Mazur.GenericFreePolynomialQuotient
