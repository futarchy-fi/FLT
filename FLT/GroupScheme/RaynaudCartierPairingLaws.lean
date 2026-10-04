/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCartierPairing

/-! # Additivity and annihilators of the finite Cartier evaluation pairing -/

@[expose] public noncomputable section
namespace ThreeAdicPlan
variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K]
  (X : FF R K)

/-- Pairing with the original zero point gives the unit. -/
@[simp] theorem FF.cartierPairing_zero_right (y : X.cartierDual.Points) :
    X.cartierPairing y 0 = 1 := by
  unfold FF.cartierPairing FF.pointCoordinate
  rw [map_zero]
  exact map_one _

/-- Addition of original points multiplies their Cartier values. -/
theorem FF.cartierPairing_add_right (y : X.cartierDual.Points) (x z : X.Points) :
    X.cartierPairing y (x + z) = X.cartierPairing y x * X.cartierPairing y z := by
  unfold FF.cartierPairing FF.pointCoordinate
  rw [map_add]
  exact map_mul _ _ _

/-- Scalar multiplication of original points raises the Cartier value to that power. -/
theorem FF.cartierPairing_nsmul_right (y : X.cartierDual.Points) (x : X.Points) (n : ℕ) :
    X.cartierPairing y (n • x) = X.cartierPairing y x ^ n := by
  induction n with
  | zero => simp
  | succ n hn => rw [succ_nsmul, X.cartierPairing_add_right, hn, pow_succ]

/-- The actual Cartier value has the same annihilating exponent as the original point. -/
theorem FF.cartierPairing_pow_eq_one (y : X.cartierDual.Points) (x : X.Points)
    (n : ℕ) (hx : n • x = 0) : X.cartierPairing y x ^ n = 1 := by
  rw [← X.cartierPairing_nsmul_right, hx, X.cartierPairing_zero_right]

end ThreeAdicPlan
