/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap

/-!
# Composition of the original node coefficient maps

Polynomial representatives give identity and composition for the specified
parameter maps, independently of the tensor presentations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
universe u
variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]

/-- Identity coefficient substitution fixes the original node ring. -/
theorem ringMap_id (t : R) : ringMap (RingHom.id R) t t rfl = RingHom.id _ := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [ringMap_mk, MvPolynomial.map_id, RingHom.id_apply]

/-- Successive substitutions compose on the original node ring. -/
theorem ringMap_comp (f : R →+* S) (g : S →+* T)
    (t : R) (s : S) (r : T) (hs : f t = s) (hr : g s = r) :
    (ringMap g s r hr).comp (ringMap f t s hs) =
      ringMap (g.comp f) t r (by rw [RingHom.comp_apply, hs, hr]) := by
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [RingHom.comp_apply, ringMap_mk, MvPolynomial.map_map]

end FLT.Mazur.PolygonSmoothing
