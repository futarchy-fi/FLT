/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismCoordinates

/-!
# Actual marked scheme sections determine coordinate evaluation transport

Equality of marked sections in the proper cubic recovers equality of their
whole affine evaluation maps. No coordinate transformation is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (hV : IsUnit V.Δ)
  (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- Preservation of actual affine marked sections preserves their entire evaluation maps. -/
theorem originIsoCoordinateHom_evaluation
    (p : Coordinate W 2 →ₐ[R] R) (q : Coordinate V 2 →ₐ[R] R)
    (h : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ integralCurveChart V 2) :
    p.comp (originIsoCoordinateHom W V hV e hb hz) = q := by
  apply AlgHom.coe_ringHom_injective
  change (CommRingCat.ofHom (p.comp (originIsoCoordinateHom W V hV e hb hz)).toRingHom).hom =
    (CommRingCat.ofHom q.toRingHom).hom
  apply congrArg CommRingCat.Hom.hom
  apply Spec.map_injective
  apply (cancel_mono (integralCurveChart V 2)).mp
  change Spec.map (CommRingCat.ofHom
    (originIsoCoordinateHom W V hV e hb hz).toRingHom ≫
      CommRingCat.ofHom p.toRingHom) ≫ _ = _
  rw [Spec.map_comp, originIsoCoordinateHom_spec, Category.assoc,
    originIsoAffineHom_inclusion]
  exact h

end FLT.Mazur.WeierstrassIntegralChart
