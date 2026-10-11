/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothingSmoothParameter
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The actual punctured complete boundary parameter

Localizing the original power-series base at its parameter constructs the
punctured base. The complementary discriminant factor is already a unit.
Thus only the original parameter is inverted, and the smooth coefficient
point exists over every coefficient ring in which two is invertible.
-/

@[expose] public noncomputable section
open AlgebraicGeometry
namespace FLT.Mazur.OneGonSmoothing
variable (R : Type) [CommRing R]

/-- The actual punctured complete coefficient ring. -/
abbrev PuncturedRing := Localization.Away (PowerSeries.X : PowerSeries R)

/-- The retained smoothing parameter on the punctured base. -/
def puncturedParameter : PuncturedRing R := algebraMap (PowerSeries R) _ PowerSeries.X

/-- The retained parameter is invertible on the actual punctured base. -/
theorem puncturedParameter_isUnit : IsUnit (puncturedParameter R) :=
  IsLocalization.Away.algebraMap_isUnit PowerSeries.X

/-- The complementary factor stays a unit on the punctured complete base. -/
theorem puncturedFactor_isUnit : IsUnit (1 + 432 * puncturedParameter R) := by
  simpa only [map_add, map_one, map_mul, map_ofNat, puncturedParameter] using
    (powerSeries_discriminant_factor_unit (R := R)).map
      (algebraMap (PowerSeries R) (PuncturedRing R))

/-- Two remains invertible after passing to power series and then puncturing. -/
theorem puncturedTwo_isUnit (h₂ : IsUnit (2 : R)) : IsUnit (2 : PuncturedRing R) := by
  simpa only [map_ofNat] using
    (h₂.map (PowerSeries.C : R →+* PowerSeries R)).map
      (algebraMap (PowerSeries R) (PuncturedRing R))

/-- The actual coefficient point on the punctured complete boundary. -/
def puncturedSmoothParameter (h₂ : IsUnit (2 : R)) :
    UniversalWeierstrass.ParameterRing →+* PuncturedRing R :=
  smoothParameter (puncturedParameter R) (puncturedTwo_isUnit R h₂)
    (puncturedParameter_isUnit R) (puncturedFactor_isUnit R)

/-- The universal smooth equation pulls back to the original punctured boundary equation. -/
theorem puncturedSmoothParameter_equation (h₂ : IsUnit (2 : R)) :
    UniversalWeierstrass.smoothEquation.map (puncturedSmoothParameter R h₂) =
      equation (puncturedParameter R) :=
  smoothParameter_equation _ _ _ _

/-- The punctured base maps to the original complete base by its localization map. -/
def puncturedBaseInclusion :
    Spec (.of (PuncturedRing R)) ⟶ Spec (.of (PowerSeries R)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries R) (PuncturedRing R)))

/-- This is an actual open immersion, rather than only a field-valued generic point. -/
instance puncturedBaseInclusion_isOpenImmersion :
    IsOpenImmersion (puncturedBaseInclusion R) := by
  unfold puncturedBaseInclusion
  infer_instance

/-- The image is exactly the complement of the original zero-parameter locus. -/
theorem puncturedBaseInclusion_opensRange :
    (puncturedBaseInclusion R).opensRange =
      PrimeSpectrum.basicOpen (PowerSeries.X : PowerSeries R) :=
  Scheme.Hom.opensRange_localizationAway (R := .of (PowerSeries R)) PowerSeries.X

/-- Every specified coefficient map with invertible parameter factors through the puncture. -/
def puncturedLift {S : Type} [CommRing S] (a : PowerSeries R →+* S)
    (ha : IsUnit (a PowerSeries.X)) : PuncturedRing R →+* S :=
  IsLocalization.Away.lift PowerSeries.X ha

/-- The punctured lift retains the original coefficient map. -/
theorem puncturedLift_comp {S : Type} [CommRing S] (a : PowerSeries R →+* S)
    (ha : IsUnit (a PowerSeries.X)) :
    (puncturedLift R a ha).comp (algebraMap (PowerSeries R) (PuncturedRing R)) = a :=
  IsLocalization.Away.lift_comp _ _

/-- The factorization through the actual punctured coefficient ring is unique. -/
theorem puncturedLift_unique {S : Type} [CommRing S] (a : PowerSeries R →+* S)
    (ha : IsUnit (a PowerSeries.X)) (b : PuncturedRing R →+* S)
    (hb : b.comp (algebraMap (PowerSeries R) (PuncturedRing R)) = a) :
    b = puncturedLift R a ha := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : PowerSeries R))
  exact hb.trans (puncturedLift_comp R a ha).symm

end FLT.Mazur.OneGonSmoothing
