/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicPushforwardH1
public import FLT.Mazur.WeierstrassCubicBaseScalars
public import FLT.Mazur.WeierstrassConstantSections
public import FLT.Mazur.ClosedPushforwardCohomology
public import FLT.Mazur.ProjectiveChartNoetherian
public import FLT.Mazur.ProperCurveGenus

/-!
# Actual first cohomology and genus of the Weierstrass cubic

Closed direct-image comparison transfers the computed H1 to the original
cubic. The scalar comparison retains its specified structure morphism.
Consequently its actual first structure cohomology has dimension one over
every field, including singular fibers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.ProjectiveSpace FLT.Mazur.ProjectiveSpace.LocalizationDegree
open FLT.Mazur.FCurve

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [Field K] (W : WeierstrassCurve K)

/-- The pushforward computation uses exactly the plane projection's field action. -/
def cubicPushforwardScalarH1Equiv :
    ModuleScalarH (baseProjection K (Fin 3)) (cubicStructurePushforward W) 1 ≃ₗ[K] K := by
  change ModuleRingH (structureScalarMap (baseProjection K (Fin 3)))
    (cubicStructurePushforward W) 1 ≃ₗ[K] K
  rw [cubicPlane_structureScalarMap]
  exact cubicPushforwardH1Equiv W

/-- Closed direct image identifies actual cohomology with the original cubic's H1. -/
def cubicClosedH1Equiv :
    ModuleScalarH (baseProjection K (Fin 3)) (cubicStructurePushforward W) 1 ≃ₗ[K]
      H1 (integralCurveStructure W) := by
  let _ : (structureModule (integralCurve W)).IsFinitePresentation :=
    unitSheaf_isFinitePresentation (integralCurve W)
  have e := closedPushforwardScalarHEquiv (integralProjectiveMap W)
    (structureModule (integralCurve W)) (baseProjection K (Fin 3)) 1
  rw [integralProjectiveMap_baseProjection] at e
  exact e

/-- The original cubic's actual first structure cohomology is the base field, linearly. -/
def integralCurveH1Equiv : H1 (integralCurveStructure W) ≃ₗ[K] K :=
  (cubicClosedH1Equiv W).symm.trans (cubicPushforwardScalarH1Equiv W)

/-- Every actual Weierstrass cubic over a field has one-dimensional first cohomology. -/
theorem integralCurveH1_finrank : Module.finrank K (H1 (integralCurveStructure W)) = 1 :=
  (integralCurveH1Equiv W).finrank_eq.trans (Module.finrank_self K)

/-- Under the dimension hypothesis, the existing actual-cohomology genus is one. -/
theorem integralCurve_genus_one (hd : topologicalKrullDim (integralCurve W) = 1) :
    curveGenus (integralCurveStructure W) hd (integralCurve_constantGlobalSections W) = 1 :=
  integralCurveH1_finrank W

end FLT.Mazur.WeierstrassIntegralChart
