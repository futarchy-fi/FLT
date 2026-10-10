/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesModelHZeroLinear
public import FLT.Mazur.PowerCohomologyReesQuotient

/-!
# Finite generation of the original H0 image Rees module

Proper coherent finiteness for the actual model transfers through the
Rees-linear H0 comparison, and then through the original image quotient.
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
  (M : X.Modules) [M.IsFinitePresentation]

/-- The original full power H0 sum is finite over its original Rees action. -/
theorem powerHZero_finite :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0
    Module.Finite (reesAlgebra J)
      (PowerCohomologySum (baseCohomologyScalars f) ((baseIdeal R J).comap f) M 0) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  let _ := globalModelSheaf_finite_cohomology f J M 0
  exact Module.Finite.equiv (modelPowerHZeroReesEquiv f J M).symm

/-- The actual cohomology-image Rees module inherits finite generation from the proper model. -/
theorem imageHZeroRees_finite :
    Module.Finite (reesAlgebra J)
      (cohomologyRees (baseCohomologyScalars f) ((baseIdeal R J).comap f)
        M J (BaseAdicCohomology.scalar_mem f J) 0) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) 0
  let _ := powerHZero_finite f J M
  exact Module.Finite.of_surjective
    (powerReesOnto (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0)
    (powerReesOnto_surjective (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) 0)

end FLT.Mazur.BaseAdicRees
