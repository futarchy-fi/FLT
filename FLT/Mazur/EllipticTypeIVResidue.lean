/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeScaledEquation
public import FLT.Mazur.EllipticNodeCoordinateFactor

/-!
# The residual quadratic in the type IV branch

After dividing singular coordinates by a generator of the maximal ideal,
the y-coordinate satisfies T² + (a₃/π)T - a₆/π². Exact depth two of b₆
makes its roots distinct, including in residue characteristic two.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  (W : WeierstrassCurve R)

/-- The divided y-coordinate of a singular point satisfies the type IV quadratic. -/
theorem typeIV_scaled_residue {π : R} (hπ : π ≠ 0)
    (hπm : π ∈ maximalIdeal R) (x y e3 e4 e6 : R)
    (h1 : W.a₁ ∈ maximalIdeal R) (h2 : W.a₂ ∈ maximalIdeal R)
    (h4m : e4 ∈ maximalIdeal R)
    (h3 : W.a₃ = π * e3) (h4 : W.a₄ = π * e4) (h6 : W.a₆ = π ^ 2 * e6)
    (he : W.toAffine.Equation (π * x) (π * y)) :
    residue R y ^ 2 + residue R e3 * residue R y = residue R e6 := by
  have h := congrArg (residue R)
    (node_scaled_equation W hπ 1 x y e3 e4 e6 (by simpa using h3)
      (by simpa using h4) (by simpa using h6) (by simpa using he))
  simpa [(residue_eq_zero_iff _).mpr hπm, (residue_eq_zero_iff _).mpr h1,
    (residue_eq_zero_iff _).mpr h2, (residue_eq_zero_iff _).mpr h4m] using h

omit [IsDomain R] in
/-- Exact depth two of b₆ gives a nonzero residual quadratic discriminant. -/
theorem typeIV_residue_discriminant_ne_zero {π : R} (hπm : π ∈ maximalIdeal R)
    (e3 e6 : R) (h3 : W.a₃ = π * e3) (h6 : W.a₆ = π ^ 2 * e6)
    (h6' : W.b₆ ∉ maximalIdeal R ^ 3) :
    residue R e3 ^ 2 + 4 * residue R e6 ≠ 0 := by
  intro hz
  have hm : e3 ^ 2 + 4 * e6 ∈ maximalIdeal R := by
    apply (residue_eq_zero_iff _).mp
    simpa only [map_add, map_pow, map_mul, map_ofNat] using hz
  apply h6'
  have hb : W.b₆ = π ^ 2 * (e3 ^ 2 + 4 * e6) := by
    rw [b₆, h3, h6]
    ring
  rw [hb, pow_succ]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hπm 2) hm

/-- A root of a quadratic with nonzero discriminant differs from its opposite root. -/
theorem typeIV_root_ne_opposite {F : Type*} [Field F] {b c t : F}
    (h : t ^ 2 + b * t = c) (hd : b ^ 2 + 4 * c ≠ 0) : t ≠ -t - b := by
  intro ht
  apply hd
  have hz : 2 * t + b = 0 := by linear_combination ht
  calc
    b ^ 2 + 4 * c = (2 * t + b) ^ 2 := by linear_combination -4 * h
    _ = 0 := by rw [hz]; ring

/-- Any two roots are equal or opposite; no algebraic closure is needed. -/
theorem typeIV_roots_eq_or_opposite {F : Type*} [Field F] {b c t u : F}
    (ht : t ^ 2 + b * t = c) (hu : u ^ 2 + b * u = c) :
    t = u ∨ t = -u - b := by
  have hp : (t - u) * (t + u + b) = 0 := by linear_combination ht - hu
  rcases mul_eq_zero.mp hp with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · right
    linear_combination h

end FLT.Mazur
