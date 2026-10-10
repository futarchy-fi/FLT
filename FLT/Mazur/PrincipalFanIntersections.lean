/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanIsomorphismOpens
public import FLT.Mazur.PrincipalOpenIntersectionModels

/-!
# Actual intersections and restriction paths in a shared-chart fan

Products of the ambient denominators compute genuine pullbacks of the
constructed overlap targets. Maps from smaller principal opens are transported
through the coordinate isomorphisms, and all nested restriction paths commute.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v

/-- Changing the two coordinate presentations preserves the explicit principal pullback. -/
theorem principalProduct_isPullback_of_isos {T : Type u} [CommRing T]
    (r s : T) {X Y : Scheme.{u}} (e : X ≅ Spec (.of (Localization.Away r)))
    (d : Y ≅ Spec (.of (Localization.Away s))) :
    IsPullback
      (PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_left r s) ≫ e.inv)
      (PrincipalLocalizationSquare.openInclusion (PrimeSpectrum.basicOpen_mul_le_right r s) ≫ d.inv)
      (e.hom ≫ PrincipalLocalizationSquare.inclusion r)
      (d.hom ≫ PrincipalLocalizationSquare.inclusion s) := by
  apply (PrincipalLocalizationSquare.product_isPullback r s).of_iso
    (Iso.refl _) e.symm d.symm (Iso.refl _)
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]
  · simp only [Iso.symm_hom, Iso.refl_hom, Category.comp_id, Iso.inv_hom_id_assoc]

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.FiniteType R A] {ι : Type v}
  {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra R (B i)]
  [∀ i, Algebra.FiniteType R (B i)]
  (a : ι → A) (b : ∀ i, B i)
  (e : ∀ i, Localization.Away (a i) ≃ₐ[R] Localization.Away (b i))

/-- The ith denominator as an element of the one shared ambient stage. -/
abbrev principalIsoFanDenominator (x : PrincipalFanIsomorphismStage a b e) (i : ι) :
    Stage R A x.val.source :=
  Ideal.Quotient.mk _ (principalRepresentative R A (a i))

/-- A smaller principal open maps to the target in its actual chosen coordinates. -/
def principalIsoFanRestriction (x : PrincipalFanIsomorphismStage a b e) (i : ι)
    {r : Stage R A x.val.source}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalIsoFanDenominator a b e x i)) :
    Spec (.of (Localization.Away r)) ⟶
      Spec (.of (PrincipalStage R (B i) (b i) (x.val.target i))) :=
  PrincipalLocalizationSquare.openInclusion h ≫ (principalIsoFanStageIso a b e x i).inv

/-- Each transported restriction is an actual open immersion. -/
instance principalIsoFanRestriction_isOpenImmersion
    (x : PrincipalFanIsomorphismStage a b e) (i : ι) {r : Stage R A x.val.source}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalIsoFanDenominator a b e x i)) :
    IsOpenImmersion (principalIsoFanRestriction a b e x i h) := by
  dsimp only [principalIsoFanRestriction]
  infer_instance

/-- Transported restrictions retain the exact map to the ambient chart. -/
@[reassoc (attr := simp)] theorem principalIsoFanRestriction_fac
    (x : PrincipalFanIsomorphismStage a b e) (i : ι) {r : Stage R A x.val.source}
    (h : PrimeSpectrum.basicOpen r ≤
      PrimeSpectrum.basicOpen (principalIsoFanDenominator a b e x i)) :
    principalIsoFanRestriction a b e x i h ≫ principalIsoFanOpen a b e x i =
      PrincipalLocalizationSquare.inclusion r := by
  dsimp only [principalIsoFanRestriction, principalIsoFanOpen]
  rw [Category.assoc, Iso.inv_hom_id_assoc, PrincipalLocalizationSquare.openInclusion_fac]

/-- Every path through an intermediate principal open gives the same target restriction. -/
theorem principalIsoFanRestriction_comp
    (x : PrincipalFanIsomorphismStage a b e) (i : ι) {r s : Stage R A x.val.source}
    (h : PrimeSpectrum.basicOpen r ≤ PrimeSpectrum.basicOpen (principalIsoFanDenominator a b e x i))
    (k : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) :
    PrincipalLocalizationSquare.openInclusion k ≫ principalIsoFanRestriction a b e x i h =
      principalIsoFanRestriction a b e x i (k.trans h) := by
  rw [← cancel_mono (principalIsoFanOpen a b e x i)]
  simp only [Category.assoc, principalIsoFanRestriction_fac,
    PrincipalLocalizationSquare.openInclusion_fac]

/-- Product denominators compute actual intersections of the finite target embeddings. -/
theorem principalIsoFanIntersection_isPullback (x : PrincipalFanIsomorphismStage a b e) (i j : ι) :
    IsPullback
      (principalIsoFanRestriction a b e x i (PrimeSpectrum.basicOpen_mul_le_left
        (principalIsoFanDenominator a b e x i) (principalIsoFanDenominator a b e x j)))
      (principalIsoFanRestriction a b e x j (PrimeSpectrum.basicOpen_mul_le_right
        (principalIsoFanDenominator a b e x i) (principalIsoFanDenominator a b e x j)))
      (principalIsoFanOpen a b e x i) (principalIsoFanOpen a b e x j) :=
  principalProduct_isPullback_of_isos _ _
    (principalIsoFanStageIso a b e x i) (principalIsoFanStageIso a b e x j)

end FLT.Mazur.FiniteTypeRelationModel
