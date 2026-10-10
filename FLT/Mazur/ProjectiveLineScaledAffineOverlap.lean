/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineScaling
public import FLT.Mazur.WeierstrassModificationXConicGeometry

/-!
# Full scaled punctured affine charts

Scaling the affine coordinate by a unit preserves the whole punctured line.
Together with the original conic parameter open, it covers the affine line.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLine
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- Scaling is an isomorphism of the entire affine chart. -/
def chartScalingIso (a : Kˣ) : chart K ≅ chart K where
  hom := chartScaling K a
  inv := chartScaling K a⁻¹
  hom_inv_id := by rw [← chartScaling_mul, mul_inv_cancel, chartScaling_one]
  inv_hom_id := by rw [← chartScaling_mul, inv_mul_cancel, chartScaling_one]

/-- The entire Laurent torus with a specified scaled affine parameter. -/
def scaledOverlapLeft (a : Kˣ) : overlap K ⟶ chart K :=
  overlapLeft K ≫ (chartScalingIso K a).hom

instance scaledOverlapLeft_open (a : Kˣ) : IsOpenImmersion (scaledOverlapLeft K a) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- Scaling retains every point of the punctured affine line. -/
theorem scaledOverlapLeft_range (a : Kˣ) : Set.range (scaledOverlapLeft K a) =
    (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change Polynomial.toLaurent (PolygonChartScaling.affine a X) ∉ y.asIdeal
    rw [PolygonChartScaling.affine_X, map_mul, Polynomial.toLaurent_C,
      Polynomial.toLaurent_X]
    exact y.asIdeal.notMem_of_isUnit
      ((a.isUnit.map LaurentPolynomial.C).mul (LaurentPolynomial.isUnit_T 1))
  · intro hx
    have hi : (chartScalingIso K a).inv x ∈ Set.range (overlapLeft K) := by
      rw [show Set.range (overlapLeft K) =
        (PrimeSpectrum.basicOpen (X : K[X]) : Set (PrimeSpectrum K[X])) from
          PrimeSpectrum.localization_away_comap_range _ _]
      change PolygonChartScaling.affine a⁻¹ X ∉ x.asIdeal
      rw [PolygonChartScaling.affine_X]
      exact (not_congr (x.asIdeal.unit_mul_mem_iff_mem ((a⁻¹).isUnit.map Polynomial.C))).mpr hx
    obtain ⟨y, hy⟩ := hi
    refine ⟨y, ?_⟩
    change (chartScalingIso K a).hom (overlapLeft K y) = x
    rw [hy, ← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl

/-- A conic parameter open and any scaled full torus exhaust the affine line. -/
theorem conicParameter_scaledTorus_cover (c : K) (a : Kˣ) (x : chart K) :
    x ∈ Set.range (Spec.map (CommRingCat.ofHom
      (algebraMap K[X] (WeierstrassModificationX.ConicParameterOpen c)))) ∨
        x ∈ Set.range (scaledOverlapLeft K a) := by
  rw [show Set.range (Spec.map (CommRingCat.ofHom
    (algebraMap K[X] (WeierstrassModificationX.ConicParameterOpen c)))) =
      (PrimeSpectrum.basicOpen (WeierstrassModificationX.conicParameterPolynomial c) :
        Set (PrimeSpectrum K[X])) from PrimeSpectrum.localization_away_comap_range _ _,
    scaledOverlapLeft_range]
  by_cases hx : X ∈ x.asIdeal
  · left
    intro hf
    have hm := x.asIdeal.mul_mem_left (C c) (x.asIdeal.pow_mem_of_mem hx 2 (by decide))
    have h1 : (1 : K[X]) ∈ x.asIdeal := by
      simpa only [WeierstrassModificationX.conicParameterPolynomial, sub_add_cancel] using
        x.asIdeal.add_mem hf hm
    exact x.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · exact Or.inr hx

end FLT.Mazur.ProjectiveLine
