/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingRingMapComposition
public import FLT.Mazur.PolygonSmoothingBranchSwapNaturality

/-!
# Whole-node identifications in compositions

Equal smoothing parameters identify the entire chart rings. These identities
allow compositions to be compared without expanding their quotient presentations.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
variable {R : Type*} [CommRing R]

/-- Identification commutes with any proof-indexed family of whole-node endomorphisms. -/
theorem nodeIdentification_square (P : R → Prop)
    (F : (t : R) → P t → ChartRing t →+* ChartRing t)
    (s t : R) (h : s = t) (hs : P s) (ht : P t) :
    (ringMap (RingHom.id R) s t h).comp (F s hs) =
      (F t ht).comp (ringMap (RingHom.id R) s t h) := by
  subst t
  rw [ringMap_id, RingHom.id_comp, RingHom.comp_id]

/-- Successive equal-parameter identifications are the single direct identification. -/
theorem nodeIdentification_comp (r s t : R) (hrs : r = s) (hst : s = t) :
    (ringMap (RingHom.id R) s t hst).comp (ringMap (RingHom.id R) r s hrs) =
      ringMap (RingHom.id R) r t (hrs.trans hst) := by
  subst s
  subst t
  rw [ringMap_id, RingHom.id_comp]

/-- Reflection respects an identification of the whole original correction. -/
theorem nodeIdentification_reflect (s t : R) (h : s = t)
    (F : ChartRing s →+* ChartRing t) (G : ChartRing t →+* ChartRing t)
    (hF : F = G.comp (ringMap (RingHom.id R) s t h)) :
    (branchSwapMap t).toRingHom.comp (F.comp (branchSwapMap s).toRingHom) =
      ((branchSwapMap t).toRingHom.comp (G.comp (branchSwapMap t).toRingHom)).comp
        (ringMap (RingHom.id R) s t h) := by
  subst s
  rw [ringMap_id, RingHom.comp_id] at hF ⊢
  rw [hF]

end FLT.Mazur.PolygonSmoothing
