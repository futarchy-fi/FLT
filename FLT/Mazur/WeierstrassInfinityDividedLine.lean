/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineCoordinates

/-!
# Divided line cubics centered at a common infinity-chart input

Subtracting two divided cubics gives a slope difference times the existing
infinity denominator. This identity retains the information at coincident
inputs; it never cancels the difference between their X coordinates.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The line cubic with its known root at the center divided out formally. -/
def infinityLineDivided (x z m d : R) : R :=
  cubicPolar W ![x, 1, z] ![1, 0, m] +
    infinityLineQuadratic W x z m * d + infinityLineLeading W m * d ^ 2

/-- The actual slope equation implies vanishing of the divided cubic. -/
theorem infinityLineDivided_of_slope {x x' z z' m : R}
    (hl : m * (x' - x) = z' - z)
    (hc : m * infinitySlopeDenominator W x' z z' =
      infinitySlopeNumerator W x x' z) :
    infinityLineDivided W x z m (x' - x) = 0 := by
  have h := infinity_line_relation W hl hc
  rw [infinityLineLeading_eq, infinityLineQuadratic_eq] at h
  exact h

/-- Subtraction compares two slopes through the same center without a coordinate divisor. -/
theorem infinityLineDivided_sub (x z l m d : R) :
    infinityLineDivided W x z l d - infinityLineDivided W x z m d =
      (l - m) * infinitySlopeDenominator W (x + d) (z + l * d) (z + m * d) := by
  simp only [infinityLineDivided, infinityLineLeading, infinityLineQuadratic,
    infinitySlopeDenominator, cubicPolar, Projective.fin3_def_ext]
  ring

/-- A known divided root splits off another factor, including on the diagonal. -/
theorem infinityLineDivided_factor {x z l a : R}
    (ha : infinityLineDivided W x z l a = 0) (d : R) :
    infinityLineDivided W x z l d =
      (d - a) * (infinityLineLeading W l * d + infinityLineQuadratic W x z l +
        infinityLineLeading W l * a) := by
  unfold infinityLineDivided at ha ⊢
  linear_combination ha

/-- Two actual divided roots give a cross relation between their line factors. -/
theorem infinityLineDivided_cross {x z l m a d : R}
    (ha : infinityLineDivided W x z l a = 0)
    (hd : infinityLineDivided W x z m d = 0) :
    (d - a) * (infinityLineLeading W l * d + infinityLineQuadratic W x z l +
        infinityLineLeading W l * a) =
      (l - m) * infinitySlopeDenominator W (x + d) (z + l * d) (z + m * d) := by
  rw [← infinityLineDivided_factor W ha, ← infinityLineDivided_sub, hd, sub_zero]

end FLT.Mazur.WeierstrassIntegralChart
