/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticFixedRetained

/-!
# A canonical unit quotient for starting thickness one

The unit is constructed integrally and transported to every arithmetic order.
This supplies the fixed-polygon maps when start = 1; it does not assert that
an arbitrary application has that starting thickness.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassModificationX
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (π : R) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "c" => algebraMap R Q

/-- The fixed quotient at thickness one is the inverse square of the original tangent unit. -/
def arithmeticStartOneQuotient : Qˣ :=
  Units.map (c).toMonoidHom ((zeroInitialTangentUnit W ha)⁻¹ ^ 2)

/-- The integral construction is also the independently normalized quotient tangent unit. -/
theorem arithmeticStartOneQuotient_eq :
    arithmeticStartOneQuotient W ha π m =
      (zeroInitialTangentUnit (W.map c) (ha.map c))⁻¹ ^ 2 := by
  rw [arithmeticStartOneQuotient, map_pow, map_inv, initialTangentUnit_map]

/-- This unit has exactly the normalized global smoothing required at start one. -/
theorem arithmeticStartOneQuotient_relation :
    parameter R π m * (arithmeticStartOneQuotient W ha π m : Q) =
      arithmeticInitialMobiusSmoothing W ha (π ^ 1) π m := by
  rw [arithmeticInitialMobiusSmoothing, ← initialTangentSmoothing_map]
  change c π * c ((↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2) =
    c (initialTangentSmoothing W ha (π ^ 1))
  rw [← map_mul, initialTangentSmoothing, pow_one, mul_comm π]

/-- The chosen unit follows the original quotient arrows at every arithmetic order. -/
theorem arithmeticStartOneQuotient_restriction :
    Units.map (restriction R π m).toMonoidHom (arithmeticStartOneQuotient W ha π (m + 1)) =
      arithmeticStartOneQuotient W ha π m := by
  apply Units.ext
  exact (restriction R π m).commutes ((↑(zeroInitialTangentUnit W ha)⁻¹ : R) ^ 2)

variable [IsDomain R] (hπ : π ≠ 0) (hs : π ∣ π ^ 1)

include hπ in
/-- The original integral divisor chosen at thickness one is necessarily one. -/
theorem startOneDivisor_eq_one : Classical.choose hs = 1 := by
  apply mul_left_cancel₀ hπ
  simpa only [pow_one, mul_one] using (Classical.choose_spec hs).symm

include hπ in
/-- The unit quotient retains the divisor used by the original first-retained map. -/
theorem arithmeticStartOneQuotient_first :
    (arithmeticStartOneQuotient W ha π m : Q) =
      (↑(zeroInitialTangentUnit (W.map c) (ha.map c))⁻¹ : Q) ^ 2 *
        c (Classical.choose hs) := by
  rw [startOneDivisor_eq_one π hπ hs, map_one, mul_one, arithmeticStartOneQuotient_eq]
  rfl

end FLT.Mazur.WeierstrassModificationX
