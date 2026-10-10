/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityCubicDifference

/-!
# Coefficients of a divided cubic on linear coordinates

The divided cubic is a homogeneous quadratic in four coordinates. Its middle
coefficient is its integral polarization; no division by two is used.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {S : Type*} [CommRing S] (A : WeierstrassCurve S)

/-- The integral polarization of the divided cubic quadratic. -/
def infinityDividedZPolar (x y z w u v r s : S) : S :=
  2 * y * v + A.a₁ * (x * v + u * y) +
    A.a₃ * ((z + w) * v + (r + s) * y) - 2 * A.a₂ * x * u -
    A.a₄ * (x * (r + s) + u * (z + w)) -
    A.a₆ * (2 * z * r + z * s + r * w + 2 * w * s)

/-- Exact quadratic expansion over every coefficient ring, including characteristic two. -/
theorem infinityCubicDividedZ_linear_expand (x y z w u v r s : S) :
    infinityCubicDividedZ (A.map C)
        (C x * X + C u) (C y * X + C v) (C z * X + C r) (C w * X + C s) =
      C (infinityCubicDividedZ A x y z w) * X ^ 2 +
        C (infinityDividedZPolar A x y z w u v r s) * X +
        C (infinityCubicDividedZ A u v r s) := by
  simp only [infinityCubicDividedZ, infinityDividedZPolar,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    map_add, map_sub, map_mul, map_pow, map_ofNat]
  ring

/-- The constant coefficient evaluates the quadratic at the constant coordinates. -/
theorem infinityCubicDividedZ_linear_coeff_zero (x y z w u v r s : S) :
    (infinityCubicDividedZ (A.map C)
      (C x * X + C u) (C y * X + C v) (C z * X + C r) (C w * X + C s)).coeff 0 =
        infinityCubicDividedZ A u v r s := by
  rw [infinityCubicDividedZ_linear_expand]
  simp

/-- The linear coefficient is the integral polarization of the two coordinate vectors. -/
theorem infinityCubicDividedZ_linear_coeff_one (x y z w u v r s : S) :
    (infinityCubicDividedZ (A.map C)
      (C x * X + C u) (C y * X + C v) (C z * X + C r) (C w * X + C s)).coeff 1 =
        infinityDividedZPolar A x y z w u v r s := by
  rw [infinityCubicDividedZ_linear_expand]
  simp

/-- The quadratic coefficient evaluates the quadratic at the direction coordinates. -/
theorem infinityCubicDividedZ_linear_coeff_two (x y z w u v r s : S) :
    (infinityCubicDividedZ (A.map C)
      (C x * X + C u) (C y * X + C v) (C z * X + C r) (C w * X + C s)).coeff 2 =
        infinityCubicDividedZ A x y z w := by
  rw [infinityCubicDividedZ_linear_expand]
  simp

/-- The constant correction from replacing the second Z coordinate by a residual. -/
theorem infinityCubicDividedZ_residual (x y z f : S) :
    infinityCubicDividedZ A x y z (z - f) =
      infinityCubicDividedZ A x y z z +
        f * (A.a₄ * x - A.a₃ * y + 3 * A.a₆ * z) - A.a₆ * f ^ 2 := by
  unfold infinityCubicDividedZ
  ring

end FLT.Mazur.WeierstrassIntegralChart
