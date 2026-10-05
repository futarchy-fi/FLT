/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticPadicKernel
public import FLT.Mazur.EllipticPrimeToResidueSpecialization
public import FLT.Mazur.EllipticUnramifiedSpecialization

/-!
# Smooth reduction of rational p-adic elliptic torsion

Over the actual p-adic integers, smooth reduction is injective on all n-torsion
at odd primes, including p-primary torsion. Odd-order torsion specializes
injectively at every rational prime. At two the remaining kernel is killed by
two. These are E₀ statements; identifying E₀ with a Néron identity component and
controlling the component quotient remain separate geometric obligations.
-/

@[expose] public noncomputable section

namespace FLT.Mazur

variable (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (padicIntegerSubring p))

/-- At odd p, smooth reduction is injective on actual n-torsion for every nonzero n. -/
theorem smoothReductionHom_padic_injOn_torsion (hp2 : p ≠ 2) (n : ℕ) (hn : n ≠ 0) :
    Set.InjOn (smoothReductionHom (padicIntegerSubring p) W) {P | n • P = 0} := by
  apply smoothReductionHom_injOn_torsion_unramified_odd _ W p hp2
    (padicIntegerSubring_maximalIdeal p) _ n hn
  change (p : ℤ_[p]) ≠ 0
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Odd-order torsion in E₀ specializes injectively at every rational prime. -/
theorem smoothReductionHom_padic_injOn_odd_torsion (n : ℕ) (hn : ¬ 2 ∣ n) :
    Set.InjOn (smoothReductionHom (padicIntegerSubring p) W) {P | n • P = 0} := by
  by_cases hp2 : p = 2
  · apply smoothReductionHom_injOn_torsion_of_not_dvd _ W p n
    simpa only [hp2] using hn
  · apply smoothReductionHom_padic_injOn_torsion p W hp2 n
    intro h
    exact hn (h ▸ dvd_zero 2)

/-- The odd-prime-order case needed for the rational prime-torsion argument. -/
theorem smoothReductionHom_padic_injOn_prime_torsion (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) :
    Set.InjOn (smoothReductionHom (padicIntegerSubring p) W) {P | ℓ • P = 0} := by
  apply smoothReductionHom_padic_injOn_odd_torsion p W ℓ
  rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two hℓ]
  exact Ne.symm hℓ2

/-- The dyadic exceptional kernel only identifies torsion points with the same double. -/
theorem smoothReductionHom_twoadic_eq_imp_two_nsmul_eq
    (W : WeierstrassCurve (padicIntegerSubring 2)) (n : ℕ) (hn : n ≠ 0)
    (P Q : ellipticE0 (padicIntegerSubring 2) W) (hP : n • P = 0) (hQ : n • Q = 0)
    (hred : smoothReductionHom (padicIntegerSubring 2) W P =
      smoothReductionHom (padicIntegerSubring 2) W Q) : 2 • P = 2 • Q := by
  apply smoothReductionHom_eq_imp_prime_nsmul_eq _ W 2
    (padicIntegerSubring_maximalIdeal 2) _ n hn P Q hP hQ hred
  norm_num

end FLT.Mazur
