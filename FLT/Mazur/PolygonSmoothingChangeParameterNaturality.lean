/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingChangeParameter

/-!
# Coefficient naturality for a changed smoothing

The explicit coordinate ring maps commute with independent scaling when both
parameters and both weights follow the given coefficient homomorphism.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (t s : R) (t' s' : S) (ht : f t = t') (hs : f s = s')
  (a b : Rˣ) (a' b' : Sˣ) (ha : f (a : R) = a') (hb : f (b : R) = b')
  (h : (a : R) * b * t = s) (h' : (a' : S) * b' * t' = s')
include ha hb

/-- Both whole-coordinate maps commute with the original coefficient homomorphism. -/
theorem ringMap_changeParameter :
    (ringMap f t t' ht).comp (changeParameter t s a b h).toRingHom =
      (changeParameter t' s' a' b' h').toRingHom.comp (ringMap f s s' hs) := by
  apply chartRing_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, ringMap_scalar]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      changeParameter_left, ringMap_left, map_mul, ringMap_scalar, ha]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      changeParameter_right, ringMap_right, map_mul, ringMap_scalar, hb]

/-- The changed chart isomorphisms preserve the full quotient maps of schemes. -/
@[reassoc] theorem changeParameterIso_ringMap :
    (changeParameterIso t' s' a' b' h').hom ≫
      Spec.map (CommRingCat.ofHom (ringMap f s s' hs)) =
        Spec.map (CommRingCat.ofHom (ringMap f t t' ht)) ≫
          (changeParameterIso t s a b h).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext
    (ringMap_changeParameter f t s t' s' ht hs a b a' b' ha hb h h').symm)

/-- The explicit inverse also retains the same original coefficient squares. -/
@[reassoc] theorem changeParameterIso_inv_ringMap :
    (changeParameterIso t' s' a' b' h').inv ≫
      Spec.map (CommRingCat.ofHom (ringMap f t t' ht)) =
        Spec.map (CommRingCat.ofHom (ringMap f s s' hs)) ≫
          (changeParameterIso t s a b h).inv := by
  apply (cancel_epi (changeParameterIso t' s' a' b' h').hom).mp
  rw [Iso.hom_inv_id_assoc, ← Category.assoc,
    changeParameterIso_ringMap f t s t' s' ht hs a b a' b' ha hb h h',
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

end FLT.Mazur.PolygonSmoothing
