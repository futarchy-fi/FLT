/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# Algebra-valued cross coordinates determine the actual cubic map

Proportional normalized coordinates give the same morphism to the whole
integral cubic. The source algebra may be nonreduced.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k : Fin 3)
  (f : Coordinate W j →ₐ[R] S) (g : Coordinate W k →ₐ[R] S)
  (h : ∀ i, f (coord W j i) = f (coord W j k) * g (coord W k i))

include h

/-- Cross coordinates construct the actual overlap, without a reducedness hypothesis. -/
theorem algebraChartCross_transition :
    ∃ c : Overlap W j k →ₐ[R] S,
      c.comp (overlapRestriction W j k) = f ∧ c.comp (transitionBase W j k) = g := by
  have hu : IsUnit (f (coord W j k)) := by
    apply isUnit_iff_exists_inv.mpr
    exact ⟨g (coord W k j), (h j).symm.trans (by rw [coord_self, map_one])⟩
  let c := overlapLift W j k f hu
  have hc := overlapLift_restriction W j k f hu
  refine ⟨c, hc, ?_⟩
  apply hom_ext
  intro i
  apply hu.mul_left_cancel
  have hr (l : Fin 3) : c (overlapCoord W j k l) = f (coord W j l) :=
    DFunLike.congr_fun hc (coord W j l)
  change f (coord W j k) * c (transitionBase W j k (coord W k i)) = _
  rw [← hr k, ← map_mul, transitionBase_coord]
  rw [← mul_assoc, mul_comm (overlapCoord W j k k), overlapInverse_mul,
    one_mul, hr, h i, hr]

/-- The algebraic cross-coordinate comparison is equality of complete cubic morphisms. -/
theorem algebraChartCross_toCurve :
    Spec.map (CommRingCat.ofHom f.toRingHom) ≫ integralCurveChart W j =
      Spec.map (CommRingCat.ofHom g.toRingHom) ≫ integralCurveChart W k := by
  obtain ⟨c, hc, hd⟩ := algebraChartCross_transition W j k f g h
  apply integralCurve_output_eq W j k _ _ (Spec.map (CommRingCat.ofHom c.toRingHom))
  · change Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp]
    exact congrArg (fun e : Coordinate W j →ₐ[R] S =>
      Spec.map (CommRingCat.ofHom e.toRingHom)) hc
  · rw [← Spec.map_comp]
    exact congrArg (fun e : Coordinate W k →ₐ[R] S =>
      Spec.map (CommRingCat.ofHom e.toRingHom)) hd

end FLT.Mazur.WeierstrassIntegralChart
