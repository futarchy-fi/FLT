/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingIdentificationCalculus

/-!
# Geometric identification of equal smoothing parameters

The equality identification of full affine nodes is precisely the spectrum
of the identity coefficient substitution, in both directions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- The canonical whole-scheme identification of equal smoothing parameters. -/
def nodeParameterIso (s t : R) (h : s = t) : chart R s ≅ chart R t :=
  eqToIso (congrArg (chart R) h)

/-- The forward geometric identification is the original coefficient map. -/
theorem nodeParameterIso_hom (s t : R) (h : s = t) :
    (nodeParameterIso s t h).hom =
      Spec.map (CommRingCat.ofHom (ringMap (RingHom.id R) t s h.symm)) := by
  subst t
  simp only [nodeParameterIso, eqToIso_refl, Iso.refl_hom, ringMap_id]
  exact (Spec.map_id _).symm

/-- The inverse geometric identification is the reverse coefficient map. -/
theorem nodeParameterIso_inv (s t : R) (h : s = t) :
    (nodeParameterIso s t h).inv =
      Spec.map (CommRingCat.ofHom (ringMap (RingHom.id R) s t h)) := by
  subst t
  simp only [nodeParameterIso, eqToIso_refl, Iso.refl_inv, ringMap_id]
  exact (Spec.map_id _).symm

/-- Coefficient substitution respects equal-parameter identifications at both ends. -/
@[reassoc] theorem nodeParameterIso_naturality {S : Type u} [CommRing S]
    (f : R →+* S) (s t : R) (h : s = t) (a b : S) (k : a = b)
    (ha : f s = a) (hb : f t = b) :
    Spec.map (CommRingCat.ofHom (ringMap f s a ha)) ≫ (nodeParameterIso s t h).hom =
      (nodeParameterIso a b k).hom ≫ Spec.map (CommRingCat.ofHom (ringMap f t b hb)) := by
  subst t
  subst b
  simp only [nodeParameterIso, eqToIso_refl, Iso.refl_hom,
    Category.id_comp]
  exact Category.comp_id _

end FLT.Mazur.PolygonSmoothing
