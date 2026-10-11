/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteH1Reduction
public import FLT.Mazur.StructureRingCohomologyIso
public import FLT.Mazur.StructureCoefficientComposition
public import FLT.Mazur.PolygonCohomologyIncidence
public import FLT.Mazur.PowerSeriesCoefficientTransport

/-!
# The actual closed parameter cohomology over its residue field

The coefficient map on the actual closed subscheme factors through the
constant coefficient. Transport to the original polygon computes H1.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve Chow.AffineBase WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- The original power-series action on the actual closed parameter subscheme. -/
def completeClosedRingScalars : PowerSeries K →+*
    Γ((compatibleProjAdicIdeal K n h).subscheme, ⊤) :=
  (compatibleProjAdicIdeal K n h).subschemeι.appTop.hom.comp
    (baseCohomologyScalars (exactVeroneseProjToBase K n h))

/-- The actual closed residue-field action is obtained from original constant series. -/
def completeClosedFieldScalars : K →+*
    Γ((compatibleProjAdicIdeal K n h).subscheme, ⊤) :=
  (completeClosedRingScalars K n h).comp PowerSeries.C

/-- Transport to the polygon retains the original power-series coefficient map. -/
theorem completeClosedRingScalars_transport :
    (completeClosedIdealIso K n h).hom.appTop.hom.comp (completeClosedRingScalars K n h) =
      (structureScalarMap (PolygonCyclicAtlas.toBase K n h)).comp
        PowerSeries.constantCoeff := by
  exact factor_scalar_transport _ _ _ (completeClosedIdealIso_hom_ι K n h) _ _
    (completeClosedFiber_scalar K n h)

/-- Transport to the polygon identifies the residue-field coefficients. -/
theorem completeClosedFieldScalars_transport :
    (completeClosedIdealIso K n h).hom.appTop.hom.comp (completeClosedFieldScalars K n h) =
      structureScalarMap (PolygonCyclicAtlas.toBase K n h) := by
  exact PowerSeriesCoefficientTransport.constants _ _ _
    (completeClosedRingScalars_transport K n h)

/-- Original power-series coefficients act on the closed fiber by their constant term. -/
theorem completeClosedRingScalars_factor :
    completeClosedRingScalars K n h =
      (completeClosedFieldScalars K n h).comp PowerSeries.constantCoeff := by
  exact PowerSeriesCoefficientTransport.factor _ _ _
    (completeClosedRingScalars_transport K n h)
    (ConcreteCategory.bijective_of_isIso (completeClosedIdealIso K n h).hom.appTop).injective

/-- Actual closed H1 is the original polygon H1 as a residue-field vector space. -/
def completeClosedH1PolygonEquiv :
    ModuleRingH (completeClosedFieldScalars K n h)
      (structureModule (compatibleProjAdicIdeal K n h).subscheme) 1 ≃ₗ[K]
        H1 (PolygonCyclicAtlas.toBase K n h) :=
  (structureRingHIsoEquiv (completeClosedIdealIso K n h)
    (completeClosedFieldScalars K n h) 1).trans
      ((moduleRingHScalarsCongr _ _ (completeClosedFieldScalars_transport K n h) _ 1).trans
        (moduleScalarHUnitEquiv (PolygonCyclicAtlas.toBase K n h) 1))

/-- The actual closed parameter cohomology has residue-field dimension one. -/
theorem completeClosedH1_finrank :
    Module.finrank K (ModuleRingH (completeClosedFieldScalars K n h)
      (structureModule (compatibleProjAdicIdeal K n h).subscheme) 1) = 1 := by
  calc
    _ = Module.finrank K (H1 (PolygonCyclicAtlas.toBase K n h)) :=
      (completeClosedH1PolygonEquiv K n h).finrank_eq
    _ = 1 := by
      have hp := PolygonCohomologyIncidence.h1_finrank K n (by omega)
        (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
        (PolygonCyclicPushout.isPushout K n h (by omega))
      exact hp

end FLT.Mazur.PolygonInfinitesimalStages
