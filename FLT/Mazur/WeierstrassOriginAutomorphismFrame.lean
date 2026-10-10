/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginAutomorphismPoles
public import FLT.Mazur.WeierstrassOriginAutomorphismExt
public import FLT.Mazur.WeierstrassChartEvaluationComparison
public import FLT.Mazur.WeierstrassTriangularFrame

/-!
# Actual automorphism rigidity from a unit-separated affine frame

The proved pole transport gives triangular coordinate images. Three fixed
original scheme sections with unit-separated coordinates then force identity
of the entire original scheme map, including over nonreduced bases.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

/-- A fixed original ring-valued scheme section fixes evaluation of every coordinate pullback. -/
theorem originAutCoordinateHom_fixed_eval (p : Coordinate W 2 →ₐ[R] R)
    (hp : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2)
    (a : Coordinate W 2) : p (originAutCoordinateHom W hΔ e hb hz a) = p a := by
  have hs := originAutCoordinateHom_fixed_section W hΔ e hb hz
    (Spec.map (CommRingCat.ofHom p.toRingHom)) hp a
  rw [specSectionHom_specMap] at hs
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of R)).inv).injective hs

include hΔ hb hz in
/-- An actual automorphism fixing a unit-separated original frame is the identity. -/
theorem originAut_eq_id_of_frame (p p' q : Coordinate W 2 →ₐ[R] R)
    (hp : Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom p.toRingHom) ≫ integralCurveChart W 2)
    (hp' : Spec.map (CommRingCat.ofHom p'.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom p'.toRingHom) ≫ integralCurveChart W 2)
    (hq : Spec.map (CommRingCat.ofHom q.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
      Spec.map (CommRingCat.ofHom q.toRingHom) ≫ integralCurveChart W 2)
    (hxx : p' (coord W 2 0) = p (coord W 2 0))
    (hxz : IsUnit (p (coord W 2 0) - q (coord W 2 0)))
    (hyy : IsUnit (p (coord W 2 1) - p' (coord W 2 1))) : e.hom = 𝟙 _ := by
  obtain ⟨r, s, hx⟩ := originAutCoordinateHom_x_triangular W hΔ e hb hz
  obtain ⟨t, v, w, hy⟩ := originAutCoordinateHom_y_triangular W hΔ e hb hz
  have ex (b : Coordinate W 2 →ₐ[R] R)
      (hf : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
        Spec.map (CommRingCat.ofHom b.toRingHom) ≫ integralCurveChart W 2) :
      r + s * b (coord W 2 0) = b (coord W 2 0) := by
    have he := originAutCoordinateHom_fixed_eval W hΔ e hb hz b hf (coord W 2 0)
    rw [hx] at he
    simpa only [map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] using he
  have ey (b : Coordinate W 2 →ₐ[R] R)
      (hf : Spec.map (CommRingCat.ofHom b.toRingHom) ≫ integralCurveChart W 2 ≫ e.hom =
        Spec.map (CommRingCat.ofHom b.toRingHom) ≫ integralCurveChart W 2) :
      t + v * b (coord W 2 0) + w * b (coord W 2 1) = b (coord W 2 1) := by
    have he := originAutCoordinateHom_fixed_eval W hΔ e hb hz b hf (coord W 2 1)
    rw [hy] at he
    simpa only [map_add, map_mul, AlgHom.commutes, Algebra.algebraMap_self,
      RingHom.id_apply] using he
  obtain ⟨hr, hs, ht, hv, hw⟩ := WeierstrassTriangularFrame.coefficients_eq
    r s t v w (p (coord W 2 0)) (p (coord W 2 1)) (p' (coord W 2 1))
    (q (coord W 2 0)) (q (coord W 2 1)) hxz hyy
    (ex p hp) (ex q hq) (ey p hp) (by simpa only [hxx] using ey p' hp') (ey q hq)
  apply originAut_eq_id_of_coordinates W hΔ e hb hz
  · simpa only [hr, hs, map_zero, map_one, zero_add, one_mul] using hx
  · simpa only [ht, hv, hw, map_zero, map_one, zero_mul, zero_add, one_mul] using hy

end FLT.Mazur.WeierstrassIntegralChart
