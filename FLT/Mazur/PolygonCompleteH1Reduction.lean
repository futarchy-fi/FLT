/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteStructureCohomology
public import FLT.Mazur.PrincipalScalarCohomologyReduction
public import Mathlib.RingTheory.LocalRing.Module

/-!
# Finite free original H1 and its actual closed reduction

Actual first cohomology of the complete family is finite free over the
original power-series ring. Its reduction modulo the original parameter
is the cohomology of the actual closed parameter subscheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve Chow.AffineBase IdealPowerScalarLift

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]

/-- Properness makes the original first cohomology a finite power-series module. -/
theorem completeStructureH1_finite :
    Module.Finite (PowerSeries K) (ModuleRingH
      (baseCohomologyScalars (exactVeroneseProjToBase K n h))
      (structureModule (exactVeroneseProj K n h)) 1) := by
  let _ := exactVeroneseProjToBase_isProper K n h
  let _ := CoherentIdealIntersection.structureModule_coherent
    (X := exactVeroneseProj K n h)
  exact proper_coherent_hasFiniteRingCohomology (exactVeroneseProjToBase K n h)
    (structureModule (exactVeroneseProj K n h)) 1

/-- Original first cohomology is free, using its proved flatness and actual finiteness. -/
theorem completeStructureH1_free :
    Module.Free (PowerSeries K) (ModuleRingH
      (baseCohomologyScalars (exactVeroneseProjToBase K n h))
      (structureModule (exactVeroneseProj K n h)) 1) := by
  let _ := completeStructureH1_finite K n h
  let _ := completeStructureH1_flat K n h
  exact Module.free_of_flat_of_isLocalRing

/-- Reducing original H1 modulo its original parameter computes actual closed H1. -/
def completeStructureH1ReductionEquiv :
    let ρ := baseCohomologyScalars (exactVeroneseProjToBase K n h)
    let M := structureModule (exactVeroneseProj K n h)
    (ModuleRingH ρ M 1 ⧸ LinearMap.range
      (DistribSMul.toLinearMap (PowerSeries K) (ModuleRingH ρ M 1)
        (PowerSeries.X : PowerSeries K))) ≃ₗ[PowerSeries K]
        ModuleRingH ((compatibleProjAdicIdeal K n h).subschemeι.appTop.hom.comp ρ)
          (structureModule (compatibleProjAdicIdeal K n h).subscheme) 1 := by
  let _ : (exactVeroneseProj K n h).IsSeparated :=
    inferInstanceAs (Proj (compatibleVeroneseGrade K n h (exactVeroneseStep K n h))).IsSeparated
  let _ := completeParameter_scalarEnd_mono K n h
  let _ : Subsingleton (ModuleH (structureModule (exactVeroneseProj K n h)) 2) :=
    completeStructureH_higher_subsingleton K n h 0
  exact (PrincipalScalarCohomologyReduction.quotientEquiv
    (baseCohomologyScalars (exactVeroneseProjToBase K n h))
    (structureModule (exactVeroneseProj K n h)) PowerSeries.X 1).trans
      (PrincipalClosedCohomology.quotientEquiv (compatibleProjAdicIdeal K n h) _
        (completeParameter_ideal K n h)
        (baseCohomologyScalars (exactVeroneseProjToBase K n h)) 1)

end FLT.Mazur.PolygonInfinitesimalStages
