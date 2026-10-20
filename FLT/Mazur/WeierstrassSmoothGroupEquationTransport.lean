/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothGroup

/-!
# Sealed equation transport for the intrinsic smooth group

Equality of equations transports the actual smooth group. The implementation
is sealed so coefficient comparisons do not expand the construction of its law.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type} [CommRing R] {U V : WeierstrassCurve R} (h : U = V)

/-- Equality transport of the full intrinsic smooth group, with a sealed implementation. -/
irreducible_def smoothEquationGroupIso : integralSmoothGroup U ≅ integralSmoothGroup V :=
  eqToIso (congrArg integralSmoothGroup h)

/-- The sealed group transport retains the literal transport of smooth schemes. -/
theorem smoothEquationGroupIso_hom_left :
    (smoothEquationGroupIso h).hom.hom.hom.hom.left =
      eqToHom (congrArg (fun W => (integralSmoothOpen W).toScheme) h) := by
  rw [smoothEquationGroupIso_def]
  subst V
  rfl

end FLT.Mazur.WeierstrassIntegralChart
