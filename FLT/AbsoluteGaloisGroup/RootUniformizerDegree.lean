/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.TotalRamification
public import FLT.Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Uniformizer roots in a finite DVR of the exact degree

The fundamental identity e f = n and the root equation force the root to
have valuation one. This identifies roots in an existing integral closure,
rather than constructing a second abstract Eisenstein model.
-/

@[expose] public noncomputable section
open IsLocalRing IsDiscreteValuationRing
namespace LocalRoot
variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

/-- A uniformizer root in an extension of its exact degree is a uniformizer;
the extension is totally ramified. -/
theorem uniformizer_of_root_of_finrank {π : R} (hπ : Irreducible π)
    {n : ℕ} (hn : 0 < n) (hdeg : Module.finrank R S = n)
    {y : S} (hy : y ^ n = algebraMap R S π) :
    Irreducible y ∧ (maximalIdeal S).ramificationIdx R = n ∧
      (maximalIdeal S).inertiaDeg R = 1 := by
  have hy0 : y ≠ 0 := by
    intro h
    have hz : algebraMap R S π = 0 := by simpa [h, hn.ne'] using hy.symm
    exact hπ.ne_zero ((FaithfulSMul.algebraMap_injective R S) (by simpa using hz))
  obtain ⟨t, ht⟩ := exists_irreducible S
  obtain ⟨k, u, hu⟩ := eq_unit_mul_pow_irreducible hy0 ht
  have hv : n * k = (maximalIdeal S).ramificationIdx R := by
    have he := congrArg (addVal S) hy
    rw [addVal_pow, hu, addVal_def' u ht k, addValMapUniformizerEqRamificationIdx hπ] at he
    rw [nsmul_eq_mul] at he
    exact_mod_cast he
  have hef := Ideal.ramificationIdx_mul_inertiaDeg_eq_finrank_of_isLocalRing
    S (IsDiscreteValuationRing.not_a_field R)
  rw [hdeg, ← hv] at hef
  have hkf : k * (maximalIdeal S).inertiaDeg R = 1 := by
    apply Nat.eq_of_mul_eq_mul_left hn
    simpa only [← mul_assoc, mul_one] using hef
  have hk : k = 1 := Nat.eq_one_of_mul_eq_one_right hkf
  refine ⟨?_, by simpa [hk] using hv.symm, Nat.eq_one_of_mul_eq_one_left hkf⟩
  rw [hu, hk, pow_one]
  exact (Associated.irreducible ⟨u, mul_comm t (u : S)⟩) ht

end LocalRoot
