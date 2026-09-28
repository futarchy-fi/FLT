/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RationalCubeValuations
public import FLT.GroupScheme.SupportedKummerCubes

/-!
# Supported Kummer parameters from valuation divisibility

If all valuations away from two and three are divisible by three, a nonzero
rational number is a product of powers of two and three with a rational cube.
Consequently its being a cube over `ℚ₃` implies its being a rational cube.

The hypotheses here concern valuations of the parameter, not ramification of
an extension. Passing from an étale group scheme to such a parameter remains
a separate comparison theorem.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Distinct prime numbers have zero valuation at each other. -/
theorem rational_prime_valuation_eq_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) : padicValRat p (q : ℚ) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  rw [padicValRat.of_nat, padicValNat_primes hpq, Nat.cast_zero]

/-- Valuations divisible by three away from two and three give an explicit
representative of the rational cube class supported on those two primes. -/
theorem exists_supported_cube_representative (a : ℚ) (ha : a ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → (3 : ℤ) ∣ padicValRat p a) :
    ∃ b : ℚ, b ≠ 0 ∧ a =
      (2 ^ padicValRat 2 a * 3 ^ padicValRat 3 a) * b ^ 3 := by
  let c : ℚ := 2 ^ padicValRat 2 a * 3 ^ padicValRat 3 a
  have h2 : (2 : ℚ) ^ padicValRat 2 a ≠ 0 := zpow_ne_zero _ (by norm_num)
  have h3 : (3 : ℚ) ^ padicValRat 3 a ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hc : c ≠ 0 := mul_ne_zero h2 h3
  have hv : ∀ p : ℕ, p.Prime → (3 : ℤ) ∣ padicValRat p (a / c) := by
    intro p hp
    let : Fact p.Prime := ⟨hp⟩
    rw [padicValRat.div ha hc, show c = _ from rfl, padicValRat.mul h2 h3,
      padicValRat.zpow, padicValRat.zpow]
    by_cases hp2 : p = 2
    · subst p
      have h22 : padicValRat 2 2 = 1 := by
        simpa using padicValRat.self (by decide : 1 < 2)
      have h23 : padicValRat 2 3 = 0 := by
        simpa using rational_prime_valuation_eq_zero (by decide : Nat.Prime 2)
          (by decide : Nat.Prime 3) (by decide : 2 ≠ 3)
      simp [h22, h23]
    by_cases hp3 : p = 3
    · subst p
      have h33 : padicValRat 3 3 = 1 := by
        simpa using padicValRat.self (by decide : 1 < 3)
      have h32 : padicValRat 3 2 = 0 := by
        simpa using rational_prime_valuation_eq_zero (by decide : Nat.Prime 3)
          (by decide : Nat.Prime 2) (by decide : 3 ≠ 2)
      simp [h33, h32]
    · have hp2' : padicValRat p 2 = 0 := by
        simpa using rational_prime_valuation_eq_zero hp (by decide) hp2
      have hp3' : padicValRat p 3 = 0 := by
        simpa using rational_prime_valuation_eq_zero hp (by decide) hp3
      simpa [hp2', hp3'] using hsupport p hp hp2 hp3
  obtain ⟨b, hb⟩ := (rational_cube_iff_valuations (a / c)).mpr hv
  have hb0 : b ≠ 0 := by
    intro hb0
    rw [hb0, zero_pow (by decide : 3 ≠ 0)] at hb
    exact div_ne_zero ha hc hb.symm
  refine ⟨b, hb0, ?_⟩
  change a = c * b ^ 3
  rw [hb, mul_div_cancel₀ _ hc]

/-- A nonzero rational cube class supported at two and three is trivial if
it becomes trivial over `ℚ₃`. -/
theorem rational_cube_of_away_valuations_and_three_adic_cube (a : ℚ) (ha : a ≠ 0)
    (hsupport : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → (3 : ℤ) ∣ padicValRat p a)
    (hlocal : ∃ x : ℚ_[3], x ^ 3 = (a : ℚ_[3])) :
    ∃ b : ℚ, b ^ 3 = a := by
  obtain ⟨b, hb, hab⟩ := exists_supported_cube_representative a ha hsupport
  exact rational_cube_of_supported_three_adic_cube a b hb _ _ hab hlocal

end ThreeAdicPlan
