/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingIdentificationGeometry

/-!
# Algebra equivalences for equal smoothing parameters

These equivalences implement the original identity coefficient substitutions,
so they can be inserted into full node corrections without changing coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]

/-- Identify whole node algebras with equal smoothing parameters. -/
def nodeParameterEquiv (s t : R) (h : s = t) : ChartRing s ≃ₐ[R] ChartRing t :=
  h ▸ AlgEquiv.refl

/-- The equivalence is exactly the original identity coefficient substitution. -/
theorem nodeParameterEquiv_toRingHom (s t : R) (h : s = t) :
    (nodeParameterEquiv s t h).toAlgHom.toRingHom = ringMap (RingHom.id R) s t h := by
  subst t
  rw [ringMap_id]
  rfl

end FLT.Mazur.PolygonSmoothing
