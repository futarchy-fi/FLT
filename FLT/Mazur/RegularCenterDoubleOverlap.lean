/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.RegularCenterRestriction
public import FLT.Mazur.PrincipalOpenIntersectionModels

/-!
# Compatibility on the actual double quotient localizations

The scheme-theoretic intersection of two input quotient opens is obtained by
inverting their product. The original denominator stays regular on that ring.
The two fraction lifts agree there, hence on the categorical intersection.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.RegularCenter

open BlowupRees

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {A B : Type u} [CommRing A] [CommRing B]
  (I : Ideal A) (φ : A →+* B) (d : B) (hI : I.map φ = Ideal.span {d})
  (hd : IsRegular d)

/-- The spectrum restriction is the canonical inclusion of a smaller principal open. -/
theorem quotientRestriction_spec (a : A) (ha : a ∈ I) (r : B)
    (hu : IsUnit (algebraMap B (Localization.Away r) (quotient I φ d hI a ha)))
    (h : PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen (quotient I φ d hI a ha)) :
    Spec.map (CommRingCat.ofHom
        (quotientRestriction I φ d hI (algebraMap B (Localization.Away r)) a ha hu)) =
      PrincipalLocalizationSquare.openInclusion h := by
  apply (cancel_mono (PrincipalLocalizationSquare.inclusion (quotient I φ d hI a ha))).mp
  rw [PrincipalLocalizationSquare.openInclusion_fac]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  exact quotientRestriction_base I φ d hI (algebraMap B (Localization.Away r)) a ha hu z

/-- The two actual local lifts agree on the full product-denominator intersection. -/
theorem quotientOpenToProj_double_overlap (a : A) (ha : a ∈ I) (b : A) (hb : b ∈ I) :
    PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_left
        (quotient I φ d hI a ha) (quotient I φ d hI b hb)) ≫
        quotientOpenToProj I φ d hI hd a ha =
      PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_right
        (quotient I φ d hI a ha) (quotient I φ d hI b hb)) ≫
        quotientOpenToProj I φ d hI hd b hb := by
  let qa := quotient I φ d hI a ha
  let qb := quotient I φ d hI b hb
  let T := Localization.Away (qa * qb)
  let ψ : B →+* T := algebraMap B T
  have haT : IsUnit (ψ qa) :=
    IsLocalization.Away.isUnit_of_dvd (qa * qb) (dvd_mul_right qa qb)
  have hbT : IsUnit (ψ qb) :=
    IsLocalization.Away.isUnit_of_dvd (qa * qb) (dvd_mul_left qb qa)
  have hdT : IsRegular (ψ d) := by
    apply isRegular_iff_mem_nonZeroDivisors.mpr
    exact IsLocalization.nonZeroDivisors_le_comap
      (M := Submonoid.powers (qa * qb)) (S := T) (isRegular_iff_mem_nonZeroDivisors.mp hd)
  rw [← quotientRestriction_spec I φ d hI a ha (qa * qb) haT,
    ← quotientRestriction_spec I φ d hI b hb (qa * qb) hbT,
    quotientOpenToProj_restrict I φ d hI ψ hd hdT,
    quotientOpenToProj_restrict I φ d hI ψ hd hdT]
  exact unitQuotientToProj_eq I (ψ.comp φ) (ψ d) (mapped_center I φ d hI ψ) hdT a ha
    (mapped_quotient_isUnit I φ d hI ψ hdT a ha haT) b hb
    (mapped_quotient_isUnit I φ d hI ψ hdT b hb hbT)

/-- The actual local lifts agree on their categorical scheme-theoretic intersection. -/
theorem quotientOpenToProj_pullback_overlap (a : A) (ha : a ∈ I) (b : A) (hb : b ∈ I) :
    pullback.fst (PrincipalLocalizationSquare.inclusion (quotient I φ d hI a ha))
        (PrincipalLocalizationSquare.inclusion (quotient I φ d hI b hb)) ≫
          quotientOpenToProj I φ d hI hd a ha =
      pullback.snd (PrincipalLocalizationSquare.inclusion (quotient I φ d hI a ha))
        (PrincipalLocalizationSquare.inclusion (quotient I φ d hI b hb)) ≫
          quotientOpenToProj I φ d hI hd b hb := by
  let h := PrincipalLocalizationSquare.product_isPullback
    (quotient I φ d hI a ha) (quotient I φ d hI b hb)
  apply (cancel_epi h.isoPullback.hom).mp
  rw [← Category.assoc, h.isoPullback_hom_fst,
    ← Category.assoc, h.isoPullback_hom_snd]
  exact quotientOpenToProj_double_overlap I φ d hI hd a ha b hb

end FLT.Mazur.RegularCenter
