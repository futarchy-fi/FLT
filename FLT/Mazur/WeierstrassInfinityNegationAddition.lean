/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityNegationFormula
public import FLT.Mazur.WeierstrassInfinityIdentityChart
public import FLT.Mazur.WeierstrassInfinityNegationChart

/-!
# The normalized infinity addition map on inverse pairs

The actual point-negation tensor evaluation specializes the polynomial inverse
formula. Cancellation by the output Y coordinate proves equality of the entire
normalized chart map with the infinity evaluation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The actual pair of a Y-chart point and its normalized negation. -/
def infinityNegationInput : ChartProduct W 1 1 →ₐ[R] InfinityNegationOpen W :=
  chartProductEvaluation W 1 1 (infinityNegationRestriction W) (infinityNegationChart W)

/-- The first input is the restricted original point. -/
theorem infinityNegationInput_left :
    (infinityNegationInput W).comp (chartProductLeft W 1 1) =
      infinityNegationRestriction W := chartProductEvaluation_left ..

/-- The second input is its constructed negation. -/
theorem infinityNegationInput_right :
    (infinityNegationInput W).comp (chartProductRight W 1 1) =
      infinityNegationChart W := chartProductEvaluation_right ..

/-- The harmless extra denominator equals one along the zero section. -/
def infinityNegationFactor : InfinityNegationOpen W :=
  1 + infinityNegationInverse W + infinityNegationInverse W ^ 2

/-- The normalization factor specializes to a reciprocal of the negated Y coordinate. -/
theorem infinityNegationInverse_map (f : InfinityNegationOpen W →ₐ[R] S) :
    f (infinityNegationInverse W) *
      (-1 - algebraMap R S W.a₁ * f (infinityNegationRestriction W (coord W 1 0)) -
        algebraMap R S W.a₃ * f (infinityNegationRestriction W (coord W 1 2))) = 1 := by
  have h := congrArg f (infinityNegationInverse_mul W)
  simpa [infinityNegationDen, chartNegationCoordinates, Projective.negY, AlgHom.commutes]
    using h

/-- The infinity addition chart sends an actual inverse pair to zero on this neighborhood. -/
theorem infinityAdditionChart_negation (f : InfinityNegationOpen W →ₐ[R] S)
    (g : InfinityAdditionOpen W →ₐ[R] S)
    (h : g.comp (infinityAdditionRestriction W) = f.comp (infinityNegationInput W))
    (hu : IsUnit (f (infinityNegationFactor W))) :
    g.comp (infinityAdditionChart W) = chartInfinityEvaluation W := by
  let q := g.comp (infinityOutputRestriction W)
  let p := q.comp (infinitySlopeRestriction W)
  let x := f (infinityNegationRestriction W (coord W 1 0))
  let z := f (infinityNegationRestriction W (coord W 1 2))
  let u := f (infinityNegationInverse W)
  let m := q (infinitySlope W)
  have hp : p = f.comp (infinityNegationInput W) := h
  have hleft (i) : infinityLeft W p i = f (infinityNegationRestriction W (coord W 1 i)) := by
    rw [hp]
    change (f.comp ((infinityNegationInput W).comp (chartProductLeft W 1 1))) _ = _
    rw [infinityNegationInput_left]
    rfl
  have hright (i) : infinityRight W p i = f (infinityNegationChart W (coord W 1 i)) := by
    rw [hp]
    change (f.comp ((infinityNegationInput W).comp (chartProductRight W 1 1))) _ = _
    rw [infinityNegationInput_right]
    rfl
  have hrx : infinityRight W p 0 = u * x := by
    rw [hright, infinityNegationChart_coord, map_mul]
    rfl
  have hrz : infinityRight W p 2 = u * z := by
    rw [hright, infinityNegationChart_coord, map_mul]
    rfl
  have hP := infinityLeft_equation W p
  rw [hleft 0, hleft 2] at hP
  have hn := infinityNegationInverse_map W f
  have hc := congrArg q (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hc
  change m * infinitySlopeDenominator (W.map (algebraMap R S))
    (infinityRight W p 0) (infinityLeft W p 2) (infinityRight W p 2) =
      infinitySlopeNumerator (W.map (algebraMap R S))
        (infinityLeft W p 0) (infinityRight W p 0) (infinityLeft W p 2) at hc
  rw [hrx, hrz, hleft 0, hleft 2] at hc
  have hd := (infinityDen_isUnit W).map q
  rw [infinityDen_map] at hd
  change IsUnit (infinitySlopeDenominator (W.map (algebraMap R S))
    (infinityRight W p 0) (infinityLeft W p 2) (infinityRight W p 2)) at hd
  rw [hrx, hrz, hleft 2] at hd
  have hl := infinityNegationSlope_mul_x (W.map (algebraMap R S)) hP hn hd hc
  have hf : IsUnit (1 + u + u ^ 2) := by
    simpa only [infinityNegationFactor, map_add, map_one, map_pow] using hu
  have hout (i) : q (infinityOutputCoordinates W i) =
      ![0, 1, 0] i * q (infinityOutputCoordinates W 1) := by
    rw [infinityOutputCoordinates_map, infinityOutputCoordinates_map]
    change infinityAdditionXYZ _ (infinityLeft W p 0) (infinityRight W p 0)
      (infinityLeft W p 2) m i = _
    rw [hrx, hleft 0, hleft 2]
    exact infinityAdditionXYZ_negation _ hl hn hf hc i
  apply hom_ext
  intro i
  apply ((infinityOutputY_isUnit W).map g).mul_left_inj.mp
  have hi := congrArg g (infinityAdditionChart_mul W i)
  rw [map_mul] at hi
  rw [chartInfinityEvaluation_coord]
  exact hi.trans (hout i)

end FLT.Mazur.WeierstrassIntegralChart
