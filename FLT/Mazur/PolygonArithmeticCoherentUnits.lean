/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticParameterCancellation

/-!
# Compatible unit factors for an arithmetic smoothing system

Restrict any choice of unit factor from one order higher. Parameter
cancellation proves that these new units agree at every adjacent order.
No compatibility of the originally chosen units is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonArithmeticStages
variable (R : Type*) [CommRing R] (π : R)
  (u : (m : ℕ) → (Quotient R π m)ˣ)

/-- Read a unit factor one order higher before using it at the current order. -/
def shiftedSmoothingUnit (m : ℕ) : (Quotient R π m)ˣ :=
  Units.map (restriction R π m).toMonoidHom (u (m + 1))

/-- The underlying scalar is the original quotient restriction of the higher unit. -/
theorem shiftedSmoothingUnit_coe (m : ℕ) :
    (shiftedSmoothingUnit R π u m : Quotient R π m) =
      restriction R π m (u (m + 1) : Quotient R π (m + 1)) := rfl

variable (c : (m : ℕ) → Quotient R π m)
  (hc : ∀ m, restriction R π m (c (m + 1)) = c m)
  (hu : ∀ m, c m = parameter R π m * ↑(u m))

include hc hu in
/-- Restricting a higher-order factor retains the exact current smoothing equation. -/
theorem shiftedSmoothingUnit_spec (m : ℕ) :
    c m = parameter R π m * ↑(shiftedSmoothingUnit R π u m) := by
  rw [← hc m, hu (m + 1), map_mul, restriction_parameter, shiftedSmoothingUnit_coe]

variable [IsDomain R] (hπ : π ≠ 0)

include hc hu hπ in
/-- The corrected units are compatible even when the original choices were independent. -/
theorem shiftedSmoothingUnit_restriction (m : ℕ) :
    Units.map (restriction R π m).toMonoidHom (shiftedSmoothingUnit R π u (m + 1)) =
      shiftedSmoothingUnit R π u m := by
  apply Units.ext
  change restriction R π m (shiftedSmoothingUnit R π u (m + 1) : Quotient R π (m + 1)) =
    restriction R π m (u (m + 1) : Quotient R π (m + 1))
  apply restriction_eq_of_parameter_mul_eq R π hπ m
  rw [← shiftedSmoothingUnit_spec R π u c hc hu, ← hu]

include hu hπ in
/-- Any already compatible factor system equals the corrected one at every order. -/
theorem shiftedSmoothingUnit_unique
    (v : (m : ℕ) → (Quotient R π m)ˣ)
    (hv : ∀ m, c m = parameter R π m * ↑(v m))
    (hvmap : ∀ m, Units.map (restriction R π m).toMonoidHom (v (m + 1)) = v m)
    (m : ℕ) : shiftedSmoothingUnit R π u m = v m := by
  rw [← hvmap m]
  apply Units.ext
  change restriction R π m (u (m + 1) : Quotient R π (m + 1)) =
    restriction R π m (v (m + 1) : Quotient R π (m + 1))
  apply restriction_eq_of_parameter_mul_eq R π hπ m
  rw [← hu, ← hv]

end FLT.Mazur.PolygonArithmeticStages
