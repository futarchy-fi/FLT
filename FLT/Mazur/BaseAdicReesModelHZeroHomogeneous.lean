/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelHomogeneous
public import FLT.Mazur.BaseAdicReesModelHZeroInclusions
public import FLT.Mazur.BaseAdicReesModelDirectImageCohomology

/-!
# Homogeneous H0 comparison with the original proper model

Original power cohomology classes assemble into H0 of the actual Rees model.
The comparison intertwines each homogeneous scalar with the original lifted
power map, before extending to arbitrary finite sums.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open scoped DirectSum

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) (J : Ideal R)
  [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation]

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso
  modelPowerHZeroEquiv modelDirectImageCohomologyEquiv

/-- Original power H0 classes identify additively with cohomology of the actual model. -/
def modelPowerHZeroToModelEquiv :
    PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0 ≃+
      ModuleRingH (modelCohomologyScalars f J) (globalModelSheaf f J M) 0 :=
  (modelPowerHZeroEquiv f J M (baseCohomologyScalars f)).symm.toAddEquiv.trans
    (modelDirectImageCohomologyEquiv f J M 0)

/-- Every original power class maps through the actual model's original degree inclusion. -/
lemma modelPowerHZeroToModelEquiv_of (n : ℕ)
    (s : ModuleRingH (baseCohomologyScalars f) (modelPowerSheaves f J M n) 0) :
    modelPowerHZeroToModelEquiv f J M (DirectSum.lof R ℕ _ n s) =
      modelDirectImageCohomologyEquiv f J M 0
        (moduleHMap (modelPowerInclusion f J M n) 0 s) := by
  change modelDirectImageCohomologyEquiv f J M 0
    ((modelPowerHZeroEquiv f J M (baseCohomologyScalars f)).symm _) = _
  apply congrArg (modelDirectImageCohomologyEquiv f J M 0)
  exact (modelPowerHZeroEquiv f J M (baseCohomologyScalars f)).symm_apply_eq.mpr
    (modelPowerHZeroEquiv_inclusion f J M (baseCohomologyScalars f) n s).symm

/-- Each homogeneous original power action equals actual multiplication on model H0. -/
lemma modelPowerHZeroToModelEquiv_monomial_of (a n : ℕ) (r : ↥(J ^ a))
    (s : ModuleRingH (baseCohomologyScalars f) (modelPowerSheaves f J M n) 0) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    modelPowerHZeroToModelEquiv f J M (Rees.monomial J a r • DirectSum.lof R ℕ _ n s) =
      Rees.monomial J a r • modelPowerHZeroToModelEquiv f J M (DirectSum.lof R ℕ _ n s) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  rw [powerReesModule_monomial_of, modelPowerHZeroToModelEquiv_of,
    modelPowerHZeroToModelEquiv_of, ← modelDirectImageCohomologyEquiv_reesEnd]
  apply congrArg (modelDirectImageCohomologyEquiv f J M 0)
  change moduleHMap (modelPowerInclusion f J M (a + n)) 0
    (moduleHMap (powerScalarMap (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) a n r) 0 s) = _
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, ← modelPowerInclusion_reesEnd,
    moduleHMap_comp, LinearMap.comp_apply]

end FLT.Mazur.BaseAdicRees
