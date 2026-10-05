/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalMultiplication

/-!
# Valuation estimates for actual E₁ multiplication

The integral quadratic remainder bounds the valuation of nP and gives equality
when the parameter is deeper than n. Unit scalars preserve its valuation, so
prime-to-residue-characteristic torsion is excluded. The sharper bound for
residue-characteristic-primary torsion is a separate coefficient-divisibility step.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]

/-- The quadratic remainder gives a valuation bound on every actual scalar multiple. -/
theorem infinityParameter_nsmul_valuation_le (n : ℕ) (P : ellipticE1 A W) :
    A.valuation (infinityParameter A W (n • P) : K) ≤
      max (A.valuation (n : K) * A.valuation (infinityParameter A W P : K))
        (A.valuation (infinityParameter A W P : K) ^ 2) := by
  obtain ⟨r, hr⟩ := infinityParameter_nsmul_expansion A W n P
  rw [hr]
  push_cast
  refine (A.valuation.map_add _ _).trans ?_
  simp only [map_mul, map_pow]
  exact max_le_max le_rfl (mul_le_of_le_one_right' (A.valuation_le_one r))

/-- A unit scalar preserves the valuation of the actual E₁ parameter. -/
theorem infinityParameter_nsmul_valuation_unit (n : ℕ) (hn : IsUnit (n : A))
    (P : ellipticE1 A W) :
    A.valuation (infinityParameter A W (n • P) : K) =
      A.valuation (infinityParameter A W P : K) := by
  obtain ⟨u, hu⟩ := infinityParameter_nsmul_unit A W n hn P
  rw [hu]
  change A.valuation ((infinityParameter A W P : K) * (u : A)) = _
  rw [map_mul, A.valuation_unit u, mul_one]

/-- Deeper than n, the linear term strictly dominates the nonlinear remainder. -/
theorem infinityParameter_nsmul_valuation_of_lt (n : ℕ) (P : ellipticE1 A W)
    (ht : A.valuation (infinityParameter A W P : K) < A.valuation (n : K)) :
    A.valuation (infinityParameter A W (n • P) : K) =
      A.valuation (n : K) * A.valuation (infinityParameter A W P : K) := by
  by_cases hp : P = 0
  · simp [hp]
  have htz : (infinityParameter A W P : K) ≠ 0 := by
    intro h
    exact hp ((infinityParameter_eq_zero_iff A W P).mp (Subtype.ext h))
  have htpos : 0 < A.valuation (infinityParameter A W P : K) :=
    (A.valuation.pos_iff).mpr htz
  obtain ⟨r, hr⟩ := infinityParameter_nsmul_expansion A W n P
  rw [hr]
  push_cast
  rw [A.valuation.map_add_eq_of_lt_left]
  · simp only [map_mul]
  · simp only [map_mul, map_pow]
    calc
      _ ≤ A.valuation (infinityParameter A W P : K) ^ 2 :=
        mul_le_of_le_one_right' (A.valuation_le_one r)
      _ < _ := by simpa only [pow_two] using mul_lt_mul_of_pos_right ht htpos

/-- A torsion point cannot have a nonzero parameter deeper than its annihilator. -/
theorem ellipticE1_eq_zero_of_nsmul_eq_zero_of_valuation_lt (n : ℕ) (P : ellipticE1 A W)
    (ht : A.valuation (infinityParameter A W P : K) < A.valuation (n : K))
    (hn : n • P = 0) : P = 0 := by
  have h := infinityParameter_nsmul_valuation_of_lt A W n P ht
  rw [hn, infinityParameter_zero] at h
  change A.valuation (0 : K) = _ at h
  rw [map_zero] at h
  have hn0 : A.valuation (n : K) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le ht)
  have hz := (mul_eq_zero.mp h.symm).resolve_left hn0
  apply (infinityParameter_eq_zero_iff A W P).mp
  exact Subtype.ext ((A.valuation.zero_iff).mp hz)

/-- Scalars prime to the residue characteristic have trivial kernel on E₁. -/
theorem ellipticE1_nsmul_eq_zero_iff_of_not_dvd (p n : ℕ) [CharP (ResidueField A) p]
    (hn : ¬ p ∣ n) (P : ellipticE1 A W) : n • P = 0 ↔ P = 0 := by
  apply ellipticE1_nsmul_eq_zero_iff A W n
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_natCast, ne_eq, CharP.cast_eq_zero_iff] using hn

end FLT.Mazur
