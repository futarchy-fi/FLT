/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelHomogeneous
public import FLT.Mazur.BaseAdicReesModelCohomologyInclusion
public import FLT.Mazur.BaseAdicReesModelDirectImageCohomology

/-!
# Homogeneous comparison in every cohomological degree with the original proper model

Original power cohomology classes assemble into cohomology of the actual Rees model.
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
  (M : X.Modules) [M.IsFinitePresentation] (q : ℕ)

attribute [local irreducible] modelPushforward modelPushforwardPowerSectionsIso
  modelPowerCohomologySumEquiv modelDirectImageCohomologyEquiv

/-- Each homogeneous original power action equals actual multiplication on model cohomology. -/
lemma modelPowerToModelEquiv_monomial_of (a n : ℕ) (r : ↥(J ^ a))
    (s : ModuleRingH (baseCohomologyScalars f) (modelPowerSheaves f J M n) q) :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    modelPowerToModelEquiv f J M q (Rees.monomial J a r • DirectSum.lof R ℕ _ n s) =
      Rees.monomial J a r • modelPowerToModelEquiv f J M q (DirectSum.lof R ℕ _ n s) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  rw [powerReesModule_monomial_of, modelPowerToModelEquiv_of,
    modelPowerToModelEquiv_of, ← modelDirectImageCohomologyEquiv_reesEnd]
  apply congrArg (modelDirectImageCohomologyEquiv f J M q)
  change moduleHMap (modelPowerInclusion f J M (a + n)) q
    (moduleHMap (powerScalarMap (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) a n r) q s) = _
  rw [← LinearMap.comp_apply, ← moduleHMap_comp, ← modelPowerInclusion_reesEnd,
    moduleHMap_comp, LinearMap.comp_apply]

end FLT.Mazur.BaseAdicRees
