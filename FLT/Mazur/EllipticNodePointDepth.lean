/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSingularDivisibility

/-!
# The common coordinate depth of a nodal point

If a₆ has exact ideal-adic depth n and a₃,a₄ are at least that deep, an
integral point cannot have both coordinates deeper than n/2. This supplies
the finite range of depths for the split component calculation. It does not
identify points at equal depth modulo E₀.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (I : Ideal R)

/-- A point with both coordinates in Iᵏ forces a₆ into I²ᵏ when a₃,a₄ lie in Iᵏ. -/
theorem node_a₆_mem_double_depth {x y : R} (he : W.toAffine.Equation x y)
    (k : ℕ) (h3 : W.a₃ ∈ I ^ k) (h4 : W.a₄ ∈ I ^ k)
    (hx : x ∈ I ^ k) (hy : y ∈ I ^ k) : W.a₆ ∈ I ^ (2 * k) := by
  simpa only [← pow_mul, Nat.mul_comm k 2] using
    a₆_mem_ideal_sq_of_equation W (I ^ k) he hx hy h3 h4

/-- Exact a₆ depth bounds the common coordinate depth by half that value. -/
theorem node_double_coordinate_depth_le {x y : R} (he : W.toAffine.Equation x y)
    (n k : ℕ) (h6 : W.a₆ ∉ I ^ (n + 1)) (h3 : W.a₃ ∈ I ^ k)
    (h4 : W.a₄ ∈ I ^ k) (hx : x ∈ I ^ k) (hy : y ∈ I ^ k) : 2 * k ≤ n := by
  by_contra hn
  exact h6 (Ideal.pow_le_pow_right (by omega)
    (node_a₆_mem_double_depth W I he k h3 h4 hx hy))

/-- For deep nodal coefficients every integral point has a coordinate of depth at most n/2. -/
theorem node_not_both_coordinates_deep {x y : R} (he : W.toAffine.Equation x y)
    (n : ℕ) (h3 : W.a₃ ∈ I ^ (n + 1)) (h4 : W.a₄ ∈ I ^ (n + 1))
    (h6 : W.a₆ ∉ I ^ (n + 1)) :
    ¬ (x ∈ I ^ (n / 2 + 1) ∧ y ∈ I ^ (n / 2 + 1)) := by
  rintro ⟨hx, hy⟩
  have h := node_double_coordinate_depth_le W I he n (n / 2 + 1) h6
    (Ideal.pow_le_pow_right (by omega) h3) (Ideal.pow_le_pow_right (by omega) h4) hx hy
  omega

end FLT.Mazur
