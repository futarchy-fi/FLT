/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionAffineCoverage
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# An actual open cover for addition on the integral affine product

If the discriminant is a unit, the two ordinary slope opens and the two
reciprocal slope opens cover the spectrum of the affine product algebra.
The reciprocal opens include the second localization at the output y-coordinate.
This covers affine inputs only; it does not construct projective addition.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The four regular addition charts for affine inputs. -/
inductive AdditionChartIndex
  | secant | tangent | verticalSecant | verticalTangent

/-- The actual coordinate rings of the four domains of regular addition. -/
def additionChartRing : AdditionChartIndex → CommRingCat
  | .secant => CommRingCat.of (SecantChart W)
  | .tangent => CommRingCat.of (TangentChart W)
  | .verticalSecant => CommRingCat.of
      (ReciprocalTargetOpen W (ratioRestriction W (verticalSecantDenominator W))
        (verticalSecantSlope W))
  | .verticalTangent => CommRingCat.of
      (ReciprocalTargetOpen W (ratioRestriction W (tangentNumerator W))
        (verticalTangentSlope W))

/-- Restriction from the affine product to an addition domain. -/
def additionChartRestriction (i : AdditionChartIndex) :
    AffineProduct W →+* additionChartRing W i :=
  match i with
  | .secant => (secantRestriction W).toRingHom
  | .tangent => (tangentRestriction W).toRingHom
  | .verticalSecant =>
      ((reciprocalTargetRestriction W _ (verticalSecantSlope W)).comp
        (ratioRestriction W (verticalSecantDenominator W))).toRingHom
  | .verticalTangent =>
      ((reciprocalTargetRestriction W _ (verticalTangentSlope W)).comp
        (ratioRestriction W (tangentNumerator W))).toRingHom

/-- The domain inclusion of a regular addition chart. -/
def additionChartInclusion (i : AdditionChartIndex) :
    Spec (additionChartRing W i) ⟶ Spec (CommRingCat.of (AffineProduct W)) :=
  Spec.map (CommRingCat.ofHom (additionChartRestriction W i))

/-- Each addition domain is an open subscheme of the affine product. -/
instance additionChartInclusion_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionChartInclusion W i) := by
  cases i with
  | secant => exact IsOpenImmersion.of_isLocalization (secantDenominator W)
  | tangent => exact IsOpenImmersion.of_isLocalization (tangentDenominator W)
  | verticalSecant =>
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (((reciprocalTargetRestriction W _ (verticalSecantSlope W)).toRingHom).comp
        (ratioRestriction W (verticalSecantDenominator W)).toRingHom)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (ratioRestriction W (verticalSecantDenominator W)).toRingHom)) :=
      IsOpenImmersion.of_isLocalization (verticalSecantDenominator W)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (reciprocalTargetRestriction W (ratioRestriction W (verticalSecantDenominator W))
          (verticalSecantSlope W)).toRingHom)) :=
      IsOpenImmersion.of_isLocalization
        (reciprocalCoordinates W (ratioRestriction W (verticalSecantDenominator W))
          (verticalSecantSlope W) 1)
    infer_instance
  | verticalTangent =>
    change IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (((reciprocalTargetRestriction W _ (verticalTangentSlope W)).toRingHom).comp
        (ratioRestriction W (tangentNumerator W)).toRingHom)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (ratioRestriction W (tangentNumerator W)).toRingHom)) :=
      IsOpenImmersion.of_isLocalization (tangentNumerator W)
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (reciprocalTargetRestriction W (ratioRestriction W (tangentNumerator W))
          (verticalTangentSlope W)).toRingHom)) :=
      IsOpenImmersion.of_isLocalization
        (reciprocalCoordinates W (ratioRestriction W (tangentNumerator W))
          (verticalTangentSlope W) 1)
    infer_instance

/-- A factorization of a residue-field point exhibits a point in a spectrum map's range. -/
theorem mem_range_comap_of_residue_lift {A B : Type*} [CommRing A] [CommRing B]
    (p : PrimeSpectrum A) (f : A →+* B) (g : B →+* p.asIdeal.ResidueField)
    (h : ∀ a, g (f a) = algebraMap A p.asIdeal.ResidueField a) :
    p ∈ Set.range (PrimeSpectrum.comap f) := by
  refine ⟨PrimeSpectrum.comap g ⟨⊥, inferInstance⟩, ?_⟩
  apply PrimeSpectrum.ext
  apply Ideal.ext
  intro a
  change g (f a) = 0 ↔ a ∈ p.asIdeal
  rw [h, Ideal.algebraMap_residueField_eq_zero]

/-- Under good reduction every prime lifts through one of the four actual chart rings. -/
theorem additionChartInclusion_covers (hΔ : IsUnit W.Δ)
    (p : PrimeSpectrum (AffineProduct W)) :
    ∃ i, p ∈ Set.range (PrimeSpectrum.comap (additionChartRestriction W i)) := by
  let f : AffineProduct W →ₐ[R] p.asIdeal.ResidueField :=
    IsScalarTower.toAlgHom R (AffineProduct W) p.asIdeal.ResidueField
  have hd : (W.map (algebraMap R p.asIdeal.ResidueField)).Δ ≠ 0 := by
    rw [WeierstrassCurve.map_Δ]
    exact (hΔ.map (algebraMap R p.asIdeal.ResidueField)).ne_zero
  rcases addition_denominators_cover_of_discriminant W f hd with hs | ht | hs | ht
  · refine ⟨.secant, mem_range_comap_of_residue_lift p _
      (ratioLift W f (secantDenominator W) hs).toRingHom ?_⟩
    exact ratioLift_restriction W f (secantDenominator W) hs
  · refine ⟨.tangent, mem_range_comap_of_residue_lift p _
      (ratioLift W f (tangentDenominator W) ht).toRingHom ?_⟩
    exact ratioLift_restriction W f (tangentDenominator W) ht
  · refine ⟨.verticalSecant, mem_range_comap_of_residue_lift p _
      (reciprocalRatioLift W f (verticalSecantDenominator W)
        (secantDenominator W) hs.1 hs.2).toRingHom ?_⟩
    exact reciprocalRatioLift_restriction W f _ _ hs.1 hs.2
  · refine ⟨.verticalTangent, mem_range_comap_of_residue_lift p _
      (reciprocalRatioLift W f (tangentNumerator W)
        (tangentDenominator W) ht.1 ht.2).toRingHom ?_⟩
    exact reciprocalRatioLift_restriction W f _ _ ht.1 ht.2

/-- The four regular addition domains form a scheme open cover in good reduction. -/
def additionAffineOpenCover (hΔ : IsUnit W.Δ) :
    (Spec (CommRingCat.of (AffineProduct W))).OpenCover where
  I₀ := AdditionChartIndex
  X i := Spec (additionChartRing W i)
  f := additionChartInclusion W
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨additionChartInclusion_covers W hΔ, inferInstance⟩

end FLT.Mazur.WeierstrassIntegralChart
