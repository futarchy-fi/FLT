/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInputSwap
public import FLT.Mazur.WeierstrassSlopeSwapFormula
public import FLT.Mazur.WeierstrassInfinityIdentityChart

/-!
# Infinity slopes and homogeneous outputs on reversed inputs

The divided-difference relation survives input reversal. The existing unit
denominator then identifies the slopes over every common algebra, including
nonreduced algebras, and the homogeneous infinity outputs agree.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- Reversing the Y-chart inputs sends every left coordinate to the right. -/
theorem infinityLeft_swap (f : ChartProduct W 1 1 →ₐ[R] S) (i : Fin 3) :
    infinityLeft W (f.comp (chartProductSwap W 1 1)) i = infinityRight W f i := by
  change (f.comp ((chartProductSwap W 1 1).comp (chartProductLeft W 1 1))) _ = _
  rw [chartProductSwap_left]
  rfl

/-- Reversing the Y-chart inputs sends every right coordinate to the left. -/
theorem infinityRight_swap (f : ChartProduct W 1 1 →ₐ[R] S) (i : Fin 3) :
    infinityRight W (f.comp (chartProductSwap W 1 1)) i = infinityLeft W f i := by
  change (f.comp ((chartProductSwap W 1 1).comp (chartProductRight W 1 1))) _ = _
  rw [chartProductSwap_right]
  rfl

variable (f g : InfinitySlopeOpen W →ₐ[R] S)
  (hbase : g.comp (infinitySlopeRestriction W) =
    (f.comp (infinitySlopeRestriction W)).comp (chartProductSwap W 1 1))

include hbase

/-- The reversed infinity slope satisfies the original divided-difference equation. -/
theorem infinitySlope_swapped_cubic :
    g (infinitySlope W) * infinityDen W (f.comp (infinitySlopeRestriction W)) =
      infinityNum W (f.comp (infinitySlopeRestriction W)) := by
  have hl := congrArg g (infinitySlope_mul_difference W)
  simp only [map_mul, map_sub] at hl
  change g (infinitySlope W) *
      (infinityRight W (g.comp (infinitySlopeRestriction W)) 0 -
        infinityLeft W (g.comp (infinitySlopeRestriction W)) 0) =
      infinityRight W (g.comp (infinitySlopeRestriction W)) 2 -
        infinityLeft W (g.comp (infinitySlopeRestriction W)) 2 at hl
  have hc := congrArg g (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hc
  dsimp only [infinityDen, infinityNum] at hc ⊢
  rw [hbase] at hl hc
  simp only [infinityLeft_swap, infinityRight_swap] at hl hc
  exact infinitySlope_cubic_swap (W.map (algebraMap R S)) hl hc

/-- The infinity slopes coincide on every common domain with reversed inputs. -/
theorem infinitySlope_swap : f (infinitySlope W) = g (infinitySlope W) := by
  have hu := (infinityDen_isUnit W).map f
  rw [infinityDen_map] at hu
  have hf := congrArg f (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hf
  exact hu.mul_left_inj.mp (hf.trans (infinitySlope_swapped_cubic W f g hbase).symm)

/-- The unnormalized infinity outputs coincide on reversed-input domains. -/
theorem infinityOutputCoordinates_swap (i : Fin 3) :
    f (infinityOutputCoordinates W i) = g (infinityOutputCoordinates W i) := by
  have hl := congrArg f (infinitySlope_mul_difference W)
  simp only [map_mul, map_sub] at hl
  change f (infinitySlope W) *
      (infinityRight W (f.comp (infinitySlopeRestriction W)) 0 -
        infinityLeft W (f.comp (infinitySlopeRestriction W)) 0) =
      infinityRight W (f.comp (infinitySlopeRestriction W)) 2 -
        infinityLeft W (f.comp (infinitySlopeRestriction W)) 2 at hl
  rw [infinityOutputCoordinates_map, infinityOutputCoordinates_map, hbase]
  simp only [infinityLeft_swap, infinityRight_swap, ← infinitySlope_swap W f g hbase]
  exact (congrFun (infinityAdditionXYZ_swap (W.map (algebraMap R S)) hl) i).symm

end FLT.Mazur.WeierstrassIntegralChart
