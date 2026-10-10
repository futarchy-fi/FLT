/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelCohomologyLinear
public import FLT.Mazur.PowerCohomologyReesQuotient

/-!
# Finite generation of the original cohomology image Rees module

Proper coherent finiteness for the actual model transfers through the
Rees-linear cohomology comparison, and then through the original image quotient.
No finite-generation or stability hypothesis is imposed on the image filtration.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation] (q : ℕ)

/-- The original full power cohomology sum is finite over its original Rees action. -/
theorem powerCohomology_finite :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    Module.Finite (reesAlgebra J)
      (PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M q) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  let _ := globalModelSheaf_finite_cohomology f J M q
  exact Module.Finite.equiv (modelPowerReesEquiv f J M q).symm

/-- The actual cohomology-image Rees module inherits finite generation from the proper model. -/
theorem imageCohomologyRees_finite :
    Module.Finite (reesAlgebra J)
      (cohomologyRees (baseCohomologyScalars f) ((baseIdeal R J).comap f)
        M J (BaseAdicCohomology.scalar_mem f J) q) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  let _ := powerCohomology_finite f J M q
  exact Module.Finite.of_surjective
    (powerReesOnto (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q)
    (powerReesOnto_surjective (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q)

end FLT.Mazur.BaseAdicRees
