/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityIdentityChart

/-!
# Scalar relations on the genuine infinity addition domain

The input maps, regular slope and homogeneous output specialize to every
coefficient algebra. Both defining slope equations, the chosen denominator
unit and the normalized output equations remain valid over nonreduced rings.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R)

/-- The first Y-chart input of the normalized infinity domain. -/
def infinityInputLeft : Coordinate W 1 →ₐ[R] InfinityAdditionOpen W :=
  (infinityAdditionRestriction W).comp (chartProductLeft W 1 1)

/-- The second Y-chart input of the normalized infinity domain. -/
def infinityInputRight : Coordinate W 1 →ₐ[R] InfinityAdditionOpen W :=
  (infinityAdditionRestriction W).comp (chartProductRight W 1 1)

/-- The regular dz/dx slope restricted to the normalized infinity domain. -/
def infinityChartSlope : InfinityAdditionOpen W :=
  infinityOutputRestriction W (infinitySlope W)

variable (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The specialized regular slope lies on the line through the actual two inputs. -/
theorem infinitySpecialization_line :
    f (infinityChartSlope W) *
        (f (infinityInputRight W (coord W 1 0)) - f (infinityInputLeft W (coord W 1 0))) =
      f (infinityInputRight W (coord W 1 2)) - f (infinityInputLeft W (coord W 1 2)) := by
  simpa only [infinityChartSlope, infinityInputLeft, infinityInputRight,
    infinityAdditionRestriction, infinityLeft, infinityRight, Function.comp_apply,
    AlgHom.comp_apply, map_mul, map_sub] using
    congrArg (f.comp (infinityOutputRestriction W)) (infinitySlope_mul_difference W)

/-- The divided cubic relation holds on the actual infinity domain, including the diagonal. -/
theorem infinitySpecialization_cubic :
    f (infinityChartSlope W) * infinitySlopeDenominator (W.map (algebraMap R S))
        (f (infinityInputRight W (coord W 1 0)))
        (f (infinityInputLeft W (coord W 1 2))) (f (infinityInputRight W (coord W 1 2))) =
      infinitySlopeNumerator (W.map (algebraMap R S))
        (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
        (f (infinityInputLeft W (coord W 1 2))) := by
  have hc := congrArg (f.comp (infinityOutputRestriction W)) (infinitySlope_mul_den W)
  rw [map_mul, infinityDen_map, infinityNum_map] at hc
  exact hc

/-- The selected infinity denominator remains a unit after arbitrary specialization. -/
theorem infinitySpecialization_den_unit :
    IsUnit (infinitySlopeDenominator (W.map (algebraMap R S))
      (f (infinityInputRight W (coord W 1 0)))
      (f (infinityInputLeft W (coord W 1 2))) (f (infinityInputRight W (coord W 1 2)))) := by
  have hu := (infinityDen_isUnit W).map (f.comp (infinityOutputRestriction W))
  rw [infinityDen_map] at hu
  exact hu

/-- Specializing the actual homogeneous output gives the dz/dx scalar formula. -/
theorem infinitySpecialization_homogeneous (i : Fin 3) :
    f (infinityOutputRestriction W (infinityOutputCoordinates W i)) =
      infinityAdditionXYZ (W.map (algebraMap R S))
        (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
        (f (infinityInputLeft W (coord W 1 2))) (f (infinityChartSlope W)) i :=
  infinityOutputCoordinates_map W (f.comp (infinityOutputRestriction W)) i

/-- Clearing the unit Y-coordinate recovers every normalized output coordinate. -/
theorem infinitySpecialization_coord_mul (i : Fin 3) :
    f (infinityAdditionChart W (coord W 1 i)) *
        infinityAdditionXYZ (W.map (algebraMap R S))
          (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
          (f (infinityInputLeft W (coord W 1 2))) (f (infinityChartSlope W)) 1 =
      infinityAdditionXYZ (W.map (algebraMap R S))
        (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
        (f (infinityInputLeft W (coord W 1 2))) (f (infinityChartSlope W)) i := by
  simpa only [map_mul, infinitySpecialization_homogeneous] using
    congrArg f (infinityAdditionChart_mul W i)

/-- The actual scalar output normalizer is a unit on the full infinity domain. -/
theorem infinitySpecialization_output_unit :
    IsUnit (infinityAdditionXYZ (W.map (algebraMap R S))
      (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
      (f (infinityInputLeft W (coord W 1 2))) (f (infinityChartSlope W)) 1) := by
  rw [← infinitySpecialization_homogeneous]
  exact (infinityOutputY_isUnit W).map f

end FLT.Mazur.WeierstrassIntegralChart
