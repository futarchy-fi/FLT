/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.NTorsionRoots

/-!
# Separability of division polynomials

The derivative of the three-division polynomial is three times the
square two-division polynomial. Coprimality of odd and two-division
polynomials therefore proves separability in characteristic different from three.
-/

@[expose] public section

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (E : WeierstrassCurve R)

/-- The derivative of the three-division polynomial is three times the
square two-division polynomial over any commutative ring. -/
theorem derivative_Ψ₃ : E.Ψ₃.derivative = 3 * E.Ψ₂Sq := by
  simp only [Ψ₃, Ψ₂Sq, derivative_add, derivative_mul, derivative_pow,
    derivative_X, derivative_C, derivative_ofNat, map_mul, map_ofNat, map_natCast]
  ring

variable {k : Type*} [Field k] (W : WeierstrassCurve k) [W.IsElliptic]

/-- The three-division polynomial of an elliptic curve is separable over
any field of characteristic different from three, including characteristic two. -/
theorem separable_preΨ_three (h3 : (3 : k) ≠ 0) : (W.preΨ 3).Separable := by
  rw [Polynomial.separable_def, preΨ_three, W.derivative_Ψ₃]
  apply IsCoprime.mul_right
  · refine ⟨0, C ((3 : k)⁻¹), ?_⟩
    simp only [zero_mul, zero_add, ← C_ofNat, ← C_mul, inv_mul_cancel₀ h3, C_1]
  · simpa only [Nat.cast_ofNat, preΨ_three, ΨSq_two] using
      W.isCoprime_preΨ_ΨSq_two (show Odd 3 by decide)

end WeierstrassCurve
