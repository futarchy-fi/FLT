/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineCoordinates
public import FLT.Mazur.WeierstrassInfinityChartSpecialization

/-!
# Collinearity of the actual normalized infinity addition

The regular infinity law satisfies the line relation for its negated sum in
every coefficient algebra. The relation follows from its constructed output
normalizer and does not require any input coordinate or difference to be a unit.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (f : InfinityAdditionOpen W →ₐ[R] S)

/-- The actual normalized output has its negation on the line through the inputs. -/
theorem infinitySpecialization_output_line :
    let V := W.map (algebraMap R S)
    let x := f (infinityInputLeft W (coord W 1 0))
    let z := f (infinityInputLeft W (coord W 1 2))
    let m := f (infinityChartSlope W)
    let x' := f (infinityAdditionChart W (coord W 1 0))
    let z' := f (infinityAdditionChart W (coord W 1 2))
    (1 + V.a₃ * (z - m * x)) * z' + (V.a₁ * (z - m * x) - m) * x' + (z - m * x) = 0 :=
  infinityAdditionXYZ_normalized_line (W.map (algebraMap R S))
    (infinitySpecialization_output_unit W f)
    (infinitySpecialization_coord_mul W f 0) (infinitySpecialization_coord_mul W f 2)

/-- The actual normalized X-coordinate satisfies the compact cleared Vieta equation. -/
theorem infinitySpecialization_output_vieta :
    let V := W.map (algebraMap R S)
    let x₁ := f (infinityInputLeft W (coord W 1 0))
    let x₂ := f (infinityInputRight W (coord W 1 0))
    let z := f (infinityInputLeft W (coord W 1 2))
    let m := f (infinityChartSlope W)
    f (infinityAdditionChart W (coord W 1 0)) *
        f (infinityOutputRestriction W (infinityOutputCoordinates W 1)) =
      infinityLineLeading V m * (2 * x₁ - x₂) - infinityLineQuadratic V x₁ z m := by
  have he := infinitySpecialization_coord_mul W f 0
  rw [← infinitySpecialization_homogeneous W f 1, infinityAdditionXYZ_x] at he
  exact he

/-- Negated output Y is the leading cubic coefficient divided by the actual output unit. -/
theorem infinitySpecialization_output_negY :
    let V := W.map (algebraMap R S)
    (-1 - V.a₁ * f (infinityAdditionChart W (coord W 1 0)) -
        V.a₃ * f (infinityAdditionChart W (coord W 1 2))) *
        f (infinityOutputRestriction W (infinityOutputCoordinates W 1)) =
      infinityLineLeading V (f (infinityChartSlope W)) := by
  dsimp only
  have hx := infinitySpecialization_coord_mul W f 0
  have hz := infinitySpecialization_coord_mul W f 2
  have hn := infinityAdditionXYZ_negY (W.map (algebraMap R S))
    (f (infinityInputLeft W (coord W 1 0))) (f (infinityInputRight W (coord W 1 0)))
    (f (infinityInputLeft W (coord W 1 2))) (f (infinityChartSlope W))
  rw [infinitySpecialization_homogeneous W f 1]
  linear_combination -(W.map (algebraMap R S)).a₁ * hx -
    (W.map (algebraMap R S)).a₃ * hz + hn

end FLT.Mazur.WeierstrassIntegralChart
