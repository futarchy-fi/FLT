/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticLocalDepth
public import FLT.Mazur.EllipticUnramifiedTorsion
public import Mathlib.Data.Nat.Factorization.Basic

/-!
# Torsion in the unramified elliptic reduction kernel

Separate an annihilator into its residue-primary and prime-to-residue factors.
For odd residue characteristic the entire torsion kernel vanishes. At two every
torsion point in the kernel is killed by two. The arithmetic hypotheses describe
the local ring and do not assume a property of the reduction map.
-/

@[expose] public section

namespace FLT.Mazur
open IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
variable [IsAdicComplete (maximalIdeal A) A]
variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]

/-- Removing the unit factor of an annihilator leaves residue-primary torsion. -/
theorem ellipticE1_exists_primary_annihilator (n : ℕ) (hn : n ≠ 0)
    (P : ellipticE1 A W) (hP : n • P = 0) : ∃ k : ℕ, p ^ k • P = 0 := by
  obtain ⟨k, m, hm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p (Fact.out : p.Prime).ne_one
  refine ⟨k, (ellipticE1_nsmul_eq_zero_iff_of_not_dvd A W p m hm _).mp ?_⟩
  simpa only [hnm, mul_nsmul] using hP

/-- Over an odd unramified local ring, the whole torsion subgroup of E₁ is trivial. -/
theorem ellipticE1_nsmul_eq_zero_iff_unramified_odd (hp2 : p ≠ 2)
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : A) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE1 A W) : n • P = 0 ↔ P = 0 := by
  constructor
  · intro hP
    obtain ⟨k, hk⟩ := ellipticE1_exists_primary_annihilator A W p n hn P hP
    exact (ellipticE1_pow_nsmul_eq_zero_iff_unramified A W p k hm
      (CharP.cast_eq_zero _ p)
      (isUnit_iff_ne_zero.mpr (by
        simpa using CharP.cast_ne_zero_of_ne_of_prime (ResidueField A) Nat.prime_two hp2))
      hp0 P).mp hk
  · rintro rfl
    exact nsmul_zero n

/-- Without an oddness assumption, every torsion point of E₁ is killed by p. -/
theorem ellipticE1_nsmul_eq_zero_of_torsion_unramified
    (hm : maximalIdeal A = Ideal.span {(p : A)}) (hp0 : (p : K) ≠ 0)
    (n : ℕ) (hn : n ≠ 0) (P : ellipticE1 A W) (hP : n • P = 0) : p • P = 0 := by
  obtain ⟨k, hk⟩ := ellipticE1_exists_primary_annihilator A W p n hn P hP
  exact ellipticE1_nsmul_eq_zero_of_pow_nsmul_eq_zero_unramified A W p k hm hp0 P hk

end FLT.Mazur
