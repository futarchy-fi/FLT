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
# Characteristic of finite fields with a three-adic algebra structure

The structure map to a finite field has nonzero kernel, which must be the
unique maximal ideal of the three-adic integers.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- Every finite field admitting an algebra structure over the three-adic integers
has characteristic three. -/
theorem charP_three_of_finite_padic_algebra
    (k : Type*) [Field k] [Finite k] [Algebra ℤ_[3] k] :
    CharP k 3 := by
  have hker : RingHom.ker (algebraMap ℤ_[3] k) ≠ ⊥ := by
    intro h
    have hinj := (RingHom.injective_iff_ker_eq_bot _).mpr h
    have : Finite ℤ_[3] := Finite.of_injective _ hinj
    exact not_finite ℤ_[3]
  have hmax : RingHom.ker (algebraMap ℤ_[3] k) = IsLocalRing.maximalIdeal ℤ_[3] :=
    IsLocalRing.eq_maximalIdeal ((RingHom.ker_isPrime _).isMaximal hker)
  apply (CharP.charP_iff_prime_eq_zero Nat.prime_three).mpr
  have hthree : (3 : ℤ_[3]) ∈ RingHom.ker (algebraMap ℤ_[3] k) := by
    rw [hmax, ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact (map_natCast _ 3).trans (CharP.cast_eq_zero (ZMod 3) 3)
  simpa only [RingHom.mem_ker, map_ofNat, Nat.cast_ofNat] using hthree

end ThreeAdicPlan
