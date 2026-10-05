/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticNodeComponentLabel

/-!
# The depth sum of three first-branch line intersections

The pairwise-product coefficient forces the intercept into the ideal power
of the two smallest depths. First-branch membership supplies one extra
power beyond the largest depth. Thus its square is deeper than the triple
product, whose exact depth must equal the depth of a₆.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve

variable {R : Type*} [CommRing R] [IsLocalRing R] {W : WeierstrassCurve R}
  {π : R} {n : ℕ} (D : SplitNodeDepth W π n)

include D

/-- The pairwise products and three first-branch intercept bounds force a deep square. -/
theorem node_line_intercept_square_mem (k j r : ℕ)
    (hk : k ≤ n / 2) (hj : j ≤ n / 2)
    (x z t l ν : R) (hx : x ∈ maximalIdeal R ^ k) (hz : z ∈ maximalIdeal R ^ j)
    (ht : t ∈ maximalIdeal R ^ r) (hl : l ∈ maximalIdeal R)
    (hνk : ν ∈ maximalIdeal R ^ (k + 1)) (hνj : ν ∈ maximalIdeal R ^ (j + 1))
    (hνr : ν ∈ maximalIdeal R ^ (r + 1))
    (hp : x * z + x * t + z * t = W.a₄ - (2 * l + W.a₁) * ν - W.a₃ * l) :
    ν ^ 2 ∈ maximalIdeal R ^ (k + j + r + 1) := by
  let s := min (k + j) (min (k + r) (j + r))
  let m := max k (max j r)
  have hs : s ≤ n + 1 := by dsimp [s]; omega
  have hm : m = k ∨ m = j ∨ m = r := by dsimp [m]; omega
  have hνm : ν ∈ maximalIdeal R ^ (m + 1) := by
    rcases hm with h | h | h
    · simpa only [h] using hνk
    · simpa only [h] using hνj
    · simpa only [h] using hνr
  have hu : IsUnit (2 * l + W.a₁) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa [show residue R l = 0 from (residue_eq_zero_iff _).mpr hl] using
      (residue_ne_zero_iff_isUnit _).mpr D.a₁_unit
  have hνs : ν ∈ maximalIdeal R ^ s := by
    apply (Ideal.unit_mul_mem_iff_mem _ hu).mp
    have he : (2 * l + W.a₁) * ν = W.a₄ - W.a₃ * l - (x * z + x * t + z * t) := by
      linear_combination hp
    rw [he]
    apply Ideal.sub_mem _
    · exact Ideal.sub_mem _ (Ideal.pow_le_pow_right hs D.a₄_mem)
        ((maximalIdeal R ^ s).mul_mem_right l (Ideal.pow_le_pow_right hs D.a₃_mem))
    · apply Ideal.add_mem _ (Ideal.add_mem _ ?_ ?_) ?_
      · exact Ideal.pow_le_pow_right (by dsimp [s]; omega)
          (show x * z ∈ maximalIdeal R ^ (k + j) by
            rw [pow_add]; exact Ideal.mul_mem_mul hx hz)
      · exact Ideal.pow_le_pow_right (by dsimp [s]; omega)
          (show x * t ∈ maximalIdeal R ^ (k + r) by
            rw [pow_add]; exact Ideal.mul_mem_mul hx ht)
      · exact Ideal.pow_le_pow_right (by dsimp [s]; omega)
          (show z * t ∈ maximalIdeal R ^ (j + r) by
            rw [pow_add]; exact Ideal.mul_mem_mul hz ht)
  have he : s + (m + 1) = k + j + r + 1 := by dsimp [s, m]; omega
  rw [← he, pow_add, pow_two]
  exact Ideal.mul_mem_mul hνs hνm

/-- A deep intercept square makes the exact triple-product depth equal the depth of a₆. -/
theorem node_triple_depth_eq [IsDomain R] (k j r : ℕ) (a c e ν : R)
    (ha : IsUnit a) (hc : IsUnit c) (he : IsUnit e)
    (hν : ν ^ 2 ∈ maximalIdeal R ^ (k + j + r + 1))
    (hp : (π ^ k * a) * (π ^ j * c) * (π ^ r * e) = ν ^ 2 + W.a₃ * ν - W.a₆) :
    k + j + r = n := by
  let s := k + j + r
  have hπ : π ∈ maximalIdeal R := D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π
  have hprod : (π ^ k * a) * (π ^ j * c) * (π ^ r * e) = π ^ s * (a * c * e) := by
    dsimp [s]
    simp only [pow_add]
    ring
  rw [hprod] at hp
  have hpm : π ^ s * (a * c * e) ∈ maximalIdeal R ^ s :=
    (maximalIdeal R ^ s).mul_mem_right _ (Ideal.pow_mem_pow hπ s)
  have hpn : π ^ s * (a * c * e) ∉ maximalIdeal R ^ (s + 1) :=
    fun h => node_factor_mem_maximalIdeal D.uniformizer_ne_zero D.maximalIdeal_eq s h
      ((ha.mul hc).mul he)
  have h3 : W.a₃ * ν ∈ maximalIdeal R ^ (n + 1) :=
    (maximalIdeal R ^ (n + 1)).mul_mem_right _ D.a₃_mem
  rcases lt_trichotomy s n with h | h | h
  · exact (hpn (hp ▸ Ideal.sub_mem _
      (Ideal.add_mem _ hν (Ideal.pow_le_pow_right (by omega) h3))
      (Ideal.pow_le_pow_right (by omega) D.a₆_mem))).elim
  · exact h
  · apply False.elim
    apply D.a₆_not_mem
    have heq : W.a₆ = ν ^ 2 + W.a₃ * ν - π ^ s * (a * c * e) := by linear_combination hp
    rw [heq]
    exact Ideal.sub_mem _ (Ideal.add_mem _ (Ideal.pow_le_pow_right (by omega) hν) h3)
      (Ideal.pow_le_pow_right (by omega) hpm)

end FLT.Mazur
