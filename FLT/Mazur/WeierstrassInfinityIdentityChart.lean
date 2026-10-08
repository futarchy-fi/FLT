/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIdentityFormula
public import FLT.Mazur.WeierstrassInfinityAdditionChart

/-!
# The infinity addition chart has two identity sections

The integral coordinate identities survive every algebra specialization.
On the normalized output domain its Y coordinate is a unit, so cancellation
proves equality of the actual chart maps when either input is infinity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Specializing the homogeneous infinity output specializes its four scalar arguments. -/
theorem infinityOutputCoordinates_map (g : InfinitySlopeOpen W →ₐ[R] S) (i : Fin 3) :
    g (infinityOutputCoordinates W i) =
      infinityAdditionXYZ (W.map (algebraMap R S))
        (infinityLeft W (g.comp (infinitySlopeRestriction W)) 0)
        (infinityRight W (g.comp (infinitySlopeRestriction W)) 0)
        (infinityLeft W (g.comp (infinitySlopeRestriction W)) 2) (g (infinitySlope W)) i := by
  have h := congrFun (infinityAdditionXYZ_map
    (W.map (algebraMap R (InfinitySlopeOpen W))) g.toRingHom
    (infinityLeft W (infinitySlopeRestriction W) 0)
    (infinityRight W (infinitySlopeRestriction W) 0)
    (infinityLeft W (infinitySlopeRestriction W) 2) (infinitySlope W)) i
  have he : (W.map (algebraMap R (InfinitySlopeOpen W))).map g.toRingHom =
      W.map (algebraMap R S) := by ext <;> exact g.commutes _
  rw [he] at h
  exact h

/-- With left input infinity, the homogeneous output is proportional to the right input. -/
theorem infinityOutputCoordinates_left_identity (g : InfinitySlopeOpen W →ₐ[R] S)
    (hx : infinityLeft W (g.comp (infinitySlopeRestriction W)) 0 = 0)
    (hz : infinityLeft W (g.comp (infinitySlopeRestriction W)) 2 = 0) (i : Fin 3) :
    g (infinityOutputCoordinates W i) =
      infinityRight W (g.comp (infinitySlopeRestriction W)) i *
        g (infinityOutputCoordinates W 1) := by
  let p := g.comp (infinitySlopeRestriction W)
  have hl := congrArg g (infinitySlope_mul_difference W)
  simp only [map_mul, map_sub] at hl
  change g (infinitySlope W) * (infinityRight W p 0 - infinityLeft W p 0) =
    infinityRight W p 2 - infinityLeft W p 2 at hl
  rw [hx, hz, sub_zero, sub_zero] at hl
  have hc := congrArg g (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hc
  change g (infinitySlope W) * infinitySlopeDenominator (W.map (algebraMap R S))
    (infinityRight W p 0) (infinityLeft W p 2) (infinityRight W p 2) =
      infinitySlopeNumerator (W.map (algebraMap R S))
        (infinityLeft W p 0) (infinityRight W p 0) (infinityLeft W p 2) at hc
  rw [hx, hz] at hc
  rw [infinityOutputCoordinates_map, infinityOutputCoordinates_map, hx, hz]
  have h := infinityAdditionXYZ_left_identity _ hl hc i
  have hr := Projective.fin3_def (infinityRight W p)
  rw [infinityRight_one] at hr
  rw [hr] at h
  exact h

/-- With right input infinity, the output is proportional to the left input. -/
theorem infinityOutputCoordinates_right_identity (g : InfinitySlopeOpen W →ₐ[R] S)
    (hx : infinityRight W (g.comp (infinitySlopeRestriction W)) 0 = 0)
    (hz : infinityRight W (g.comp (infinitySlopeRestriction W)) 2 = 0) (i : Fin 3) :
    g (infinityOutputCoordinates W i) =
      infinityLeft W (g.comp (infinitySlopeRestriction W)) i *
        g (infinityOutputCoordinates W 1) := by
  let p := g.comp (infinitySlopeRestriction W)
  have hl := congrArg g (infinitySlope_mul_difference W)
  simp only [map_mul, map_sub] at hl
  change g (infinitySlope W) * (infinityRight W p 0 - infinityLeft W p 0) =
    infinityRight W p 2 - infinityLeft W p 2 at hl
  rw [hx, hz, zero_sub, zero_sub, mul_neg, neg_inj] at hl
  have hc := congrArg g (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hc
  change g (infinitySlope W) * infinitySlopeDenominator (W.map (algebraMap R S))
    (infinityRight W p 0) (infinityLeft W p 2) (infinityRight W p 2) =
      infinitySlopeNumerator (W.map (algebraMap R S))
        (infinityLeft W p 0) (infinityRight W p 0) (infinityLeft W p 2) at hc
  rw [hx, hz] at hc
  rw [infinityOutputCoordinates_map, infinityOutputCoordinates_map, hx]
  have h := infinityAdditionXYZ_right_identity _ hl hc i
  have hr := Projective.fin3_def (infinityLeft W p)
  rw [infinityLeft_one] at hr
  rw [hr] at h
  exact h

/-- The normalized infinity chart restricts to the right input along the left zero section. -/
theorem infinityAdditionChart_left_identity (f : Coordinate W 1 →ₐ[R] S)
    (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : g.comp (infinityAdditionRestriction W) =
      f.comp (chartProductAtLeftInfinity W 1)) :
    g.comp (infinityAdditionChart W) = f := by
  let q := g.comp (infinityOutputRestriction W)
  have he : q.comp (infinitySlopeRestriction W) =
      f.comp (chartProductAtLeftInfinity W 1) := h
  have hl (i) : infinityLeft W (q.comp (infinitySlopeRestriction W)) i = ![0, 1, 0] i := by
    rw [he]
    change (f.comp ((chartProductAtLeftInfinity W 1).comp
      (chartProductLeft W 1 1))) (coord W 1 i) = _
    rw [chartProductAtLeftInfinity_left, AlgHom.comp_apply, chartInfinityEvaluation_coord]
    fin_cases i <;> simp
  have hr (i) : infinityRight W (q.comp (infinitySlopeRestriction W)) i = f (coord W 1 i) := by
    rw [he]
    change (f.comp ((chartProductAtLeftInfinity W 1).comp
      (chartProductRight W 1 1))) (coord W 1 i) = _
    rw [chartProductAtLeftInfinity_right, AlgHom.comp_id]
  apply hom_ext
  intro i
  apply ((infinityOutputY_isUnit W).map g).mul_left_inj.mp
  have hi := congrArg g (infinityAdditionChart_mul W i)
  rw [map_mul] at hi
  exact hi.trans ((infinityOutputCoordinates_left_identity W q (hl 0) (hl 2) i).trans
    (congrArg (fun a => a * q (infinityOutputCoordinates W 1)) (hr i)))

/-- The normalized infinity chart restricts to the left input along the right zero section. -/
theorem infinityAdditionChart_right_identity (f : Coordinate W 1 →ₐ[R] S)
    (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : g.comp (infinityAdditionRestriction W) =
      f.comp (chartProductAtRightInfinity W 1)) :
    g.comp (infinityAdditionChart W) = f := by
  let q := g.comp (infinityOutputRestriction W)
  have he : q.comp (infinitySlopeRestriction W) =
      f.comp (chartProductAtRightInfinity W 1) := h
  have hr (i) : infinityRight W (q.comp (infinitySlopeRestriction W)) i = ![0, 1, 0] i := by
    rw [he]
    change (f.comp ((chartProductAtRightInfinity W 1).comp
      (chartProductRight W 1 1))) (coord W 1 i) = _
    rw [chartProductAtRightInfinity_right, AlgHom.comp_apply, chartInfinityEvaluation_coord]
    fin_cases i <;> simp
  have hl (i) : infinityLeft W (q.comp (infinitySlopeRestriction W)) i = f (coord W 1 i) := by
    rw [he]
    change (f.comp ((chartProductAtRightInfinity W 1).comp
      (chartProductLeft W 1 1))) (coord W 1 i) = _
    rw [chartProductAtRightInfinity_left, AlgHom.comp_id]
  apply hom_ext
  intro i
  apply ((infinityOutputY_isUnit W).map g).mul_left_inj.mp
  have hi := congrArg g (infinityAdditionChart_mul W i)
  rw [map_mul] at hi
  exact hi.trans ((infinityOutputCoordinates_right_identity W q (hr 0) (hr 2) i).trans
    (congrArg (fun a => a * q (infinityOutputCoordinates W 1)) (hl i)))

end FLT.Mazur.WeierstrassIntegralChart
