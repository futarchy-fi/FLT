/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Characteristic of finite fields with a p-adic algebra structure

The structure map to a finite field has nonzero kernel, which must be the
unique maximal ideal of the p-adic integers.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Every finite field admitting an algebra structure over the p-adic integers
has characteristic p. -/
theorem charP_of_finite_padic_algebra
    (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [Finite k] [Algebra ℤ_[p] k] :
    CharP k p := by
  have hker : RingHom.ker (algebraMap ℤ_[p] k) ≠ ⊥ := by
    intro h
    have hinj := (RingHom.injective_iff_ker_eq_bot _).mpr h
    have : Finite ℤ_[p] := Finite.of_injective _ hinj
    exact not_finite ℤ_[p]
  have hmax : RingHom.ker (algebraMap ℤ_[p] k) = IsLocalRing.maximalIdeal ℤ_[p] :=
    IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal hker)
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  have hprime : (p : ℤ_[p]) ∈ RingHom.ker (algebraMap ℤ_[p] k) := by
    rw [hmax, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact (map_natCast _ p).trans (CharP.cast_eq_zero (ZMod p) p)
  simpa only [RingHom.mem_ker, map_natCast] using hprime

/-- The three-adic specialization of the finite-residue-field calculation. -/
theorem charP_three_of_finite_padic_algebra
    (k : Type*) [Field k] [Finite k] [Algebra ℤ_[3] k] :
    CharP k 3 :=
  charP_of_finite_padic_algebra 3 k

end ThreeAdicPlan
