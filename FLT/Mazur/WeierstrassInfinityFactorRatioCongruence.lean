/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityLaurentMaps

/-!
# The full infinity factor ratio is congruent to the inverse tangent unit

The congruence retains the original polynomial root and extended incidence
coordinate. It holds for every nilpotent coefficient ideal, at every order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2 : W.a₂ ∈ I) (h3 : W.a₃ ∈ I) (h4 : W.a₄ ∈ I) (h6 : W.a₆ ∈ I)
  (s b3 : R) (r : Polynomial R) (hr : r ∈ I.map Polynomial.C) (hb : b3 ∈ I)
local notation "B" => Coordinate W 1
local notation "c" => algebraMap R B
local notation "J" => I.map c
local notation "v" => nilpotentInfinityIncidence W I hI h2 h3 h4 h6 s
local notation "t" => nilpotentInfinityTangentUnit W I hI h2 h3 h4 h6
local notation "a" => infinityFactorRatioUnit W I hI h2 h3 h4 h6 s b3 r hr hb

include hr in
/-- The cleared small factor reduces to one in the original coefficient ideal. -/
theorem infinitySmallFactor_sub_one_mem :
    infinitySmallFactor W I hI h2 h3 h4 h6 s r - 1 ∈ J := by
  have hv := NilpotentPolynomialInverse.eval₂_mem I c r hr v
  simpa only [infinitySmallFactor, sub_sub_cancel_left] using
    (J).neg_mem ((J).mul_mem_left (coord W 1 0) hv)

include hr hb in
/-- The cleared opposite factor reduces to the linear tangent factor. -/
theorem infinityOppositeFactor_sub_tangent_mem :
    infinityOppositeFactor W I hI h2 h3 h4 h6 s b3 r - (t : B) ∈ J := by
  have hv := NilpotentPolynomialInverse.eval₂_mem I c r hr v
  have hb' := (J).mul_mem_right v (Ideal.mem_map_of_mem c hb)
  convert (J).mul_mem_left (coord W 1 0) ((J).add_mem hv hb') using 1
  rw [nilpotentInfinityTangentUnit_val, infinityOppositeFactor]
  ring

/-- The complete original regular ratio differs from the inverse tangent only in J. -/
theorem infinityFactorRatioUnit_sub_inverse_tangent_mem :
    (a : B) - (↑t⁻¹ : B) ∈ J := by
  let q := Ideal.Quotient.mk J
  have hs : q (infinitySmallFactor W I hI h2 h3 h4 h6 s r) = 1 := by
    simpa only [map_one] using
      Ideal.Quotient.eq.mpr (infinitySmallFactor_sub_one_mem W I hI h2 h3 h4 h6 s r hr)
  have ho : q (infinityOppositeFactor W I hI h2 h3 h4 h6 s b3 r) = q (t : B) :=
    Ideal.Quotient.eq.mpr
      (infinityOppositeFactor_sub_tangent_mem W I hI h2 h3 h4 h6 s b3 r hr hb)
  have he := congrArg q
    (infinityFactorRatioUnit_denominator W I hI h2 h3 h4 h6 s b3 r hr hb)
  rw [map_mul, ho, hs] at he
  apply Ideal.Quotient.eq.mp
  change q (a : B) = q (↑t⁻¹ : B)
  apply ((t).isUnit.map q).mul_right_cancel
  calc
    q (a : B) * q (t : B) = 1 := he
    _ = q (↑t⁻¹ : B) * q (t : B) := by rw [← map_mul, Units.inv_mul, map_one]

end FLT.Mazur.WeierstrassIntegralChart
