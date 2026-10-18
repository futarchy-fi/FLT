/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingParameterEquiv

/-!
# Coefficient squares for equal-parameter identifications

Parameter transport commutes with the original coefficient substitutions.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

/-- Identifying equal parameters commutes with the actual coefficient ring map. -/
theorem nodeParameterEquiv_restriction (f : R →+* S)
    (r r' : R) (s s' : S) (hr : r = r') (hs : s = s')
    (h : f r = s) (h' : f r' = s') :
    (ringMap f r' s' h').comp (nodeParameterEquiv r r' hr).toRingHom =
      (nodeParameterEquiv s s' hs).toRingHom.comp (ringMap f r s h) := by
  subst r'
  subst s'
  rfl

end FLT.Mazur.PolygonSmoothing
