/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesCohomologyFinite

/-!
# Finite generation of the genuine power-cohomology kernel

The kernel of the original Rees comparison is a submodule of the geometrically
finite full cohomology sum over a Noetherian Rees algebra. Its elements retain
exactly the original degreewise inclusion kernels.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening FLT.Mazur.Chow.AffineBase
open FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{0}} [IsNoetherianRing R]
  {X : Scheme.{0}} [X.IsSeparated] (f : X ⟶ Spec R) [IsProper f] (J : Ideal R)
  [IsLocallyNoetherian X] [TopologicalSpace.NoetherianSpace X]
  (M : X.Modules) [M.IsFinitePresentation] (q : ℕ)

/-- The kernel of the actual Rees comparison is finitely generated over the Rees algebra. -/
theorem powerCohomology_kernel_fg :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    (LinearMap.ker (powerReesComparison (baseCohomologyScalars f)
      ((baseIdeal R J).comap f) M J (BaseAdicCohomology.scalar_mem f J) q)).FG := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  let _ := powerCohomology_finite f J M q
  exact IsNoetherian.noetherian _

/-- The actual inclusion kernel, with its inherited Rees action, is a finite module. -/
theorem powerCohomology_kernel_finite :
    let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
      M J (BaseAdicCohomology.scalar_mem f J) q
    Module.Finite (reesAlgebra J)
      (LinearMap.ker (powerReesComparison (baseCohomologyScalars f)
        ((baseIdeal R J).comap f) M J (BaseAdicCohomology.scalar_mem f J) q)) := by
  let _ := powerReesModule (baseCohomologyScalars f) ((baseIdeal R J).comap f)
    M J (BaseAdicCohomology.scalar_mem f J) q
  exact Module.Finite.iff_fg.mpr (powerCohomology_kernel_fg f J M q)

end FLT.Mazur.BaseAdicRees
