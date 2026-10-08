/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTripleResidualSystem

/-!
# Eliminating the opposite cross residual

Combining the full cubic comparison with reciprocity gives a polynomial
syzygy whose minor coefficient is the primitive own-input pair. This keeps
all coefficients and works over rings with zero divisors.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

variable {S : Type*} [CommRing S]

/-- Reciprocity eliminates the opposite residual from the entire cubic, not only its constant. -/
theorem infinity_residual_elimination (P Q D : S[X]) (a e f m r : S)
    (hc : P * X - Q * (C (1 + a * e) * X - C m) = (C r * X + C f) * D)
    (hr : e + f + a * e * f + r * m = 0) :
    C m * P + (P - Q - C r * D) * (X - C m) =
      C e * (C a * Q * X - C (1 + a * f) * D) := by
  have h := congrArg (C : S →+* S[X]) hr
  simp only [map_add, map_mul, map_zero] at h
  simp only [map_add, map_mul, map_one] at hc ⊢
  linear_combination hc + D * h

/-- With zero first residual, the primitive pair multiplies the minor into the defect ideal. -/
theorem infinity_residual_elimination_of_zero (P Q D : S[X]) (a f m r : S)
    (hc : P * X - Q * (C (1 + a * 0) * X - C m) = (C r * X + C f) * D)
    (hr : 0 + f + a * 0 * f + r * m = 0) :
    C m * P = -(P - Q - C r * D) * (X - C m) := by
  have h := infinity_residual_elimination P Q D a 0 f m r hc hr
  simp only [map_zero, zero_mul] at h
  linear_combination h

/-- A regular own-input pair cancels the minor once the first residual and defect vanish. -/
theorem infinity_residual_minor_eq_zero (P Q D : S[X]) (a f m r : S)
    (hP : IsRegular P)
    (hc : P * X - Q * (C (1 + a * 0) * X - C m) = (C r * X + C f) * D)
    (hr : 0 + f + a * 0 * f + r * m = 0)
    (hd : P - Q - C r * D = 0) : m = 0 := by
  have h := infinity_residual_elimination_of_zero P Q D a f m r hc hr
  rw [hd, neg_zero, zero_mul] at h
  have hm : C m = (0 : S[X]) := hP.2 <| by simpa only [zero_mul] using h
  exact C_injective (by simpa only [map_zero] using hm)

end FLT.Mazur.WeierstrassIntegralChart
