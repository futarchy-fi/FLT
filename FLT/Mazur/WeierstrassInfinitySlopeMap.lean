/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLineCoordinates

/-!
# Base change of the infinity secant coefficients

These identities transport divided cubic equations into polynomial algebras
without expanding the scheme maps or the tensor-product constructions.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S]
  (W : WeierstrassCurve R) (f : R →+* S)

/-- The divided cubic denominator commutes with every coefficient homomorphism. -/
theorem infinitySlopeDenominator_map (x z z' : R) :
    infinitySlopeDenominator (W.map f) (f x) (f z) (f z') =
      f (infinitySlopeDenominator W x z z') := by
  simp only [infinitySlopeDenominator, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    map_sub, map_add, map_one, map_mul, map_pow]

/-- The divided cubic numerator commutes with every coefficient homomorphism. -/
theorem infinitySlopeNumerator_map (x x' z : R) :
    infinitySlopeNumerator (W.map f) (f x) (f x') (f z) =
      f (infinitySlopeNumerator W x x' z) := by
  simp only [infinitySlopeNumerator, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₄, map_sub, map_add, map_mul, map_pow]

/-- The leading line coefficient is compatible with arbitrary base change. -/
theorem infinityLineLeading_map (m : R) :
    infinityLineLeading (W.map f) (f m) = f (infinityLineLeading W m) := by
  simp only [infinityLineLeading, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, map_sub, map_neg, map_one, map_mul, map_pow]

/-- The line relation survives coefficient extension. -/
theorem infinitySlope_line_map {x x' z z' m : R}
    (h : m * (x' - x) = z' - z) :
    f m * (f x' - f x) = f z' - f z := by
  simpa only [map_mul, map_sub] using congrArg f h

/-- The divided relation survives coefficient extension, including on tangent inputs. -/
theorem infinitySlope_cubic_map {x x' z z' m : R}
    (h : m * infinitySlopeDenominator W x' z z' = infinitySlopeNumerator W x x' z) :
    f m * infinitySlopeDenominator (W.map f) (f x') (f z) (f z') =
      infinitySlopeNumerator (W.map f) (f x) (f x') (f z) := by
  rw [infinitySlopeDenominator_map, infinitySlopeNumerator_map, ← map_mul, h]

end FLT.Mazur.WeierstrassIntegralChart
