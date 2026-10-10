/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginIsomorphismPoles
public import FLT.Mazur.WeierstrassTriangularCoordinates

/-!
# Unit leading coordinates of actual origin-preserving isomorphisms

The inverse scheme isomorphism supplies the inverse triangular map. Invertible
leading coefficients are consequences of the original geometric isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

/-- Pulling back along the inverse scheme isomorphism is a left inverse on coordinates. -/
theorem originIsoCoordinateHom_leftInverse : Function.LeftInverse
    (originIsoCoordinateHom V W hW e.symm
      (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz))
    (originIsoCoordinateHom W V hV e hb hz) := by
  let f := originIsoCoordinateHom W V hV e hb hz
  let g := originIsoCoordinateHom V W hW e.symm
    (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz)
  have hfg : g.comp f = AlgHom.id R (Coordinate V 2) := by
    apply AlgHom.coe_ringHom_injective
    change (CommRingCat.ofHom (g.comp f).toRingHom).hom =
      (CommRingCat.ofHom (RingHom.id (Coordinate V 2))).hom
    apply congrArg CommRingCat.Hom.hom
    apply Spec.map_injective
    change Spec.map (CommRingCat.ofHom f.toRingHom ≫ CommRingCat.ofHom g.toRingHom) = _
    rw [Spec.map_comp, originIsoCoordinateHom_spec, originIsoCoordinateHom_spec]
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact (originIsoAffineIso W V hV e hb hz hW).inv_hom_id
  exact fun a => DFunLike.congr_fun hfg a

include hW in
/-- Both leading coefficients in any triangular expression are units. -/
theorem originIsoCoordinateHom_isUnit (r s t v w : R)
    (hx : originIsoCoordinateHom W V hV e hb hz (coord V 2 0) =
      algebraMap R _ r + algebraMap R _ s * coord W 2 0)
    (hy : originIsoCoordinateHom W V hV e hb hz (coord V 2 1) =
      algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
        algebraMap R _ w * coord W 2 1) : IsUnit s ∧ IsUnit w := by
  obtain ⟨r', s', hx'⟩ := originIsoCoordinateHom_x_triangular V W hW e.symm
    (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz)
  obtain ⟨t', v', w', hy'⟩ := originIsoCoordinateHom_y_triangular V W hW e.symm
    (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz)
  exact triangular_leftInverse_isUnit W V _ _
    (originIsoCoordinateHom_leftInverse W V hW hV e hb hz)
    r s t v w r' s' t' v' w' hx hy hx' hy'

include hW in
/-- Arbitrary actual marked isomorphisms have triangular coordinates with unit scales. -/
theorem originIsoCoordinateHom_exists_units : ∃ (r t v : R) (s w : Rˣ),
    originIsoCoordinateHom W V hV e hb hz (coord V 2 0) =
      algebraMap R _ r + algebraMap R _ (s : R) * coord W 2 0 ∧
    originIsoCoordinateHom W V hV e hb hz (coord V 2 1) =
      algebraMap R _ t + algebraMap R _ v * coord W 2 0 +
        algebraMap R _ (w : R) * coord W 2 1 := by
  obtain ⟨r, s, hx⟩ := originIsoCoordinateHom_x_triangular W V hV e hb hz
  obtain ⟨t, v, w, hy⟩ := originIsoCoordinateHom_y_triangular W V hV e hb hz
  obtain ⟨⟨su, rfl⟩, ⟨wu, rfl⟩⟩ := originIsoCoordinateHom_isUnit W V hW hV e hb hz
    r s t v w hx hy
  exact ⟨r, t, v, su, wu, hx, hy⟩

end FLT.Mazur.WeierstrassIntegralChart
