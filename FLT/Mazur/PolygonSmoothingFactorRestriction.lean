/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonSmoothingIdentificationGeometry

/-!
# Coefficient squares for whole node factors

An explicit ring square gives the geometric square, also after identifying
an equal output smoothing. This retains both coordinates of the full node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
  (f : R →+* S) (s t : R) (a b : S) (hs : f s = a) (ht : f t = b)
  (E : ChartRing t ≃ₐ[R] ChartRing s) (F : ChartRing b ≃ₐ[S] ChartRing a)
  (h : (ringMap f s a hs).comp E.toAlgHom.toRingHom =
    F.toAlgHom.toRingHom.comp (ringMap f t b ht))

include h

/-- The explicit full ring square gives the corresponding spectrum square. -/
@[reassoc] theorem nodeFactorIso_restriction :
    Spec.map (CommRingCat.ofHom (ringMap f s a hs)) ≫
        (Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op).hom =
      (Scheme.Spec.mapIso F.toRingEquiv.toCommRingCatIso.op).hom ≫
        Spec.map (CommRingCat.ofHom (ringMap f t b ht)) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext h)

/-- Identifying equal output parameters preserves the same original coefficient square. -/
@[reassoc] theorem normalizedNodeFactorIso_restriction
    (t' : R) (b' : S) (he : t = t') (hf : b = b') (ht' : f t' = b') :
    Spec.map (CommRingCat.ofHom (ringMap f s a hs)) ≫
        ((Scheme.Spec.mapIso E.toRingEquiv.toCommRingCatIso.op) ≪≫
          nodeParameterIso t t' he).hom =
      ((Scheme.Spec.mapIso F.toRingEquiv.toCommRingCatIso.op) ≪≫
          nodeParameterIso b b' hf).hom ≫
        Spec.map (CommRingCat.ofHom (ringMap f t' b' ht')) := by
  simp only [Iso.trans_hom]
  rw [← Category.assoc, nodeFactorIso_restriction f s t a b hs ht E F h,
    Category.assoc, nodeParameterIso_naturality f t t' he b b' hf ht ht',
    Category.assoc]

end FLT.Mazur.PolygonSmoothing
