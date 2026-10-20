/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonGeneralizedCurve
public import FLT.Mazur.GeneralizedCurveBaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Generic and boundary fibers of the integral one-gon degeneration

The actual family over Z[[t]] has smooth generic fiber and the original pinched
one-gon at every zero-parameter field specialization. These maps retain the
original arithmetic base and do not replace it with a constant field family.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.IntegralOneGonSpecializations

open OneGonSmoothing ArithmeticOneGonGeneralizedCurve ArithmeticOneGonFieldFibers

/-- The specified generic field of the integral power-series base. -/
abbrev GenericField := FractionRing (PowerSeries ℤ)

/-- The actual generic point map to the original arithmetic base. -/
def genericMap : Spec (.of GenericField) ⟶ Spec (.of (PowerSeries ℤ)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries ℤ) GenericField))

/-- The actual generic fiber of the integral degeneration is smooth of dimension one. -/
theorem generic_smooth_dimension :
    SmoothOfRelativeDimension 1 (integralPowerSeriesCurve.baseChange genericMap).curve.hom := by
  apply cartesian_relativeDimension PowerSeries.X powerSeries_discriminant_factor_unit
    GenericField (algebraMap (PowerSeries ℤ) GenericField) _ _ _ (IsPullback.of_hasPullback _ _)
  exact (map_ne_zero_iff _ (IsFractionRing.injective (PowerSeries ℤ) GenericField)).mpr
    PowerSeries.X_ne_zero

variable (K : Type) [Field K]

/-- Constant coefficient followed by the integer specialization is the boundary ring map. -/
def boundaryHom : PowerSeries ℤ →+* K :=
  (Int.castRingHom K).comp PowerSeries.constantCoeff

/-- The boundary map kills the specified smoothing parameter. -/
theorem boundaryHom_parameter : boundaryHom K PowerSeries.X = 0 := by
  simp [boundaryHom]

/-- The original arithmetic boundary test over the chosen field. -/
def boundaryMap : Spec (.of K) ⟶ Spec (.of (PowerSeries ℤ)) :=
  Spec.map (CommRingCat.ofHom (boundaryHom K))

/-- The actual zero-parameter fiber is isomorphic to the original pinched one-gon. -/
def boundaryIso : OneGonGluing.scheme K ≅
    (integralPowerSeriesCurve.baseChange (boundaryMap K)).curve.left := by
  let _ := (boundaryHom K).toAlgebra
  exact zeroParameterFiberIso K PowerSeries.X (boundaryHom_parameter K)

/-- This boundary comparison preserves the original structure map over the field. -/
@[reassoc] theorem boundaryIso_toBase :
    (boundaryIso K).hom ≫ (integralPowerSeriesCurve.baseChange (boundaryMap K)).curve.hom =
      OneGonGluing.toBase K := by
  let _ := (boundaryHom K).toAlgebra
  exact zeroParameterFiberIso_snd K PowerSeries.X (boundaryHom_parameter K)

end FLT.Mazur.IntegralOneGonSpecializations
