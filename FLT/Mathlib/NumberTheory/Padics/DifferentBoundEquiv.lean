/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.NumberTheory.Padics.DifferentBound

/-!
# Different bounds in another presentation of the p-adic base

Transport only the uniformizer and integer divisibility across the base
isomorphism. The different remains over the original base ring.
-/

@[expose] public noncomputable section

namespace IsDiscreteValuationRing

variable {p : ℕ} [Fact p.Prime] {R S : Type}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R]
  [Finite (IsLocalRing.ResidueField R)]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- The uniform prime-power bound is invariant under a presentation of the base. -/
theorem prime_pow_mem_different_of_base_equiv (e : R ≃+* ℤ_[p]) (N : ℕ)
    (hN : Module.finrank R S ≤ N) :
    (p : S) ^ (N + 1) ∈ differentIdeal R S := by
  have hπ : Irreducible (p : R) := by
    simpa only [map_natCast] using
      (MulEquiv.irreducible_iff (f := e.symm)).mpr PadicInt.irreducible_p
  have : Module.Free R S := Module.free_of_finite_type_torsion_free'
  have hn : 0 < Module.finrank R S := Module.finrank_pos
  have hd : (Module.finrank R S : R) ∣ (p : R) ^ N := by
    have h := (PadicInt.natCast_dvd_prime_pow_self (p := p) hn).trans
      (pow_dvd_pow (p : ℤ_[p]) hN)
    simpa only [map_natCast, map_pow] using _root_.map_dvd e.symm h
  have hmem := finrank_mul_uniformizer_mem_different_of_henselian (S := S) hπ
  have h := (differentIdeal R S).mem_of_dvd
    (_root_.map_dvd (algebraMap R S) (mul_dvd_mul_right hd (p : R))) hmem
  simpa only [map_mul, map_natCast, map_pow, ← pow_succ] using h

end IsDiscreteValuationRing
