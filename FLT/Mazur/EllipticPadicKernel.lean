/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticUnramifiedKernel
public import FLT.Mazur.PadicValuationRing

/-!
# Torsion in the actual rational p-adic elliptic kernel

Over the ordinary p-adic integers every arithmetic hypothesis in the
unramified kernel theorem is proved. For odd p there is no torsion in E₁;
over the two-adic integers every torsion point in E₁ is killed by two.
These statements concern actual points of any integral Weierstrass equation.
-/

@[expose] public noncomputable section

namespace FLT.Mazur
open IsLocalRing

variable (p : ℕ) [Fact p.Prime] (W : WeierstrassCurve (padicIntegerSubring p))

/-- At any odd rational prime the local elliptic kernel is torsion-free. -/
theorem ellipticE1_padic_nsmul_eq_zero_iff (hp2 : p ≠ 2)
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE1 (padicIntegerSubring p) W) :
    n • P = 0 ↔ P = 0 := by
  apply ellipticE1_nsmul_eq_zero_iff_unramified_odd _ W p hp2
    (padicIntegerSubring_maximalIdeal p) _ n hn P
  change (p : ℤ_[p]) ≠ 0
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- At every rational prime, including two, kernel torsion is killed by that prime. -/
theorem ellipticE1_padic_prime_nsmul_eq_zero_of_torsion
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE1 (padicIntegerSubring p) W)
    (hP : n • P = 0) : p • P = 0 := by
  apply ellipticE1_nsmul_eq_zero_of_torsion_unramified _ W p
    (padicIntegerSubring_maximalIdeal p) _ n hn P hP
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Prime-to-p torsion in the actual local elliptic kernel is zero, including at two. -/
theorem ellipticE1_padic_nsmul_eq_zero_iff_of_not_dvd
    (n : ℕ) (hn : ¬ p ∣ n) (P : ellipticE1 (padicIntegerSubring p) W) :
    n • P = 0 ↔ P = 0 :=
  ellipticE1_nsmul_eq_zero_iff_of_not_dvd _ W p n hn P

/-- In particular the two-adic torsion kernel has exponent at most two. -/
theorem ellipticE1_twoadic_two_nsmul_eq_zero_of_torsion
    (W : WeierstrassCurve (padicIntegerSubring 2)) (n : ℕ) (hn : n ≠ 0)
    (P : ellipticE1 (padicIntegerSubring 2) W) (hP : n • P = 0) : 2 • P = 0 :=
  ellipticE1_padic_prime_nsmul_eq_zero_of_torsion 2 W n hn P hP

end FLT.Mazur
