/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.HenselianDifferentBound
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# A uniform degree bound for the different over the p-adic integers

For a finite Henselian DVR extension of rank at most `N`, the different
contains `p^(N+1)`. This coarse bound applies without a total-ramification
hypothesis and suffices for bounded-degree Hermite arguments.
-/

@[expose] public noncomputable section

namespace PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- A positive integer divides a power of p whose exponent is at most that integer. -/
theorem natCast_dvd_prime_pow_self {n : ℕ} (hn : 0 < n) :
    (n : ℤ_[p]) ∣ (p : ℤ_[p]) ^ n := by
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (Nat.cast_ne_zero.mpr hn.ne' : (n : ℤ_[p]) ≠ 0) (irreducible_p (p := p))
  have hd : (p : ℤ_[p]) ^ m ∣ (n : ℤ_[p]) := by
    rw [hu]
    exact dvd_mul_left _ _
  have hd' : p ^ m ∣ n := by
    have := (pow_p_dvd_int_iff (p := p) m n).mp (by simpa using hd)
    exact_mod_cast this
  have hm : m ≤ n := (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le.trans
    (Nat.le_of_dvd hn hd')
  rw [hu]
  simpa using (pow_dvd_pow (p : ℤ_[p]) hm)

end PadicInt

namespace IsDiscreteValuationRing

variable {p : ℕ} [Fact p.Prime] {S : Type} [CommRing S] [IsDomain S]
  [IsDiscreteValuationRing S] [HenselianLocalRing S] [Algebra ℤ_[p] S]
  [Module.Finite ℤ_[p] S] [FaithfulSMul ℤ_[p] S]

/-- A rank bound gives an explicit power of p in the different of the full DVR. -/
theorem prime_pow_mem_different_of_finrank_le (N : ℕ)
    (hN : Module.finrank ℤ_[p] S ≤ N) :
    (p : S) ^ (N + 1) ∈ differentIdeal ℤ_[p] S := by
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv (ZMod p) PadicInt.residueField.symm.toEquiv
  have : Module.Free ℤ_[p] S := Module.free_of_finite_type_torsion_free'
  have hn : 0 < Module.finrank ℤ_[p] S := Module.finrank_pos
  have hmem := finrank_mul_uniformizer_mem_different_of_henselian
    (S := S) (PadicInt.irreducible_p (p := p))
  have hd : ((Module.finrank ℤ_[p] S : ℤ_[p]) * p) ∣ (p : ℤ_[p]) ^ (N + 1) := by
    rw [pow_succ]
    exact mul_dvd_mul_right
      ((PadicInt.natCast_dvd_prime_pow_self hn).trans (pow_dvd_pow _ hN)) _
  have hm := (differentIdeal ℤ_[p] S).mem_of_dvd
    (_root_.map_dvd (algebraMap ℤ_[p] S) hd) hmem
  simpa only [map_pow, map_natCast] using hm

end IsDiscreteValuationRing
