/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UnramifiedDifferent
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.UnramifiedSubalgebra
public import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# A different bound for finite Henselian DVR extensions

Construct an unramified coefficient DVR with the full residue field, apply
the totally ramified bound over it, and use transitivity of the different.
The resulting scalar bound uses the rank over the original base ring.
-/

@[expose] public noncomputable section

universe u
open IsLocalRing
open scoped nonZeroDivisors

namespace IsDiscreteValuationRing

variable {R S : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CharZero R] [Finite (ResidueField R)]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [HenselianLocalRing S]
  [Algebra R S] [Module.Finite R S] [FaithfulSMul R S]

attribute [local instance] FractionRing.liftAlgebra

/-- The different contains the base uniformizer times the full extension rank. -/
theorem finrank_mul_uniformizer_mem_different_of_henselian
    {π : R} (hπ : Irreducible π) :
    algebraMap R S ((Module.finrank R S : R) * π) ∈ differentIdeal R S := by
  obtain ⟨C, iC, dC, vC, aRC, fRC, aCS, tRCS, hinj, hπC, hres⟩ :=
    existsUnramifiedCoefficientRing (S := S) hπ
  have : FaithfulSMul C S := (faithfulSMul_iff_algebraMap_injective C S).mpr hinj
  have : FaithfulSMul R C := (faithfulSMul_iff_algebraMap_injective R C).mpr (by
    intro x y h
    apply FaithfulSMul.algebraMap_injective R S
    simpa only [IsScalarTower.algebraMap_apply R C S] using
      congrArg (algebraMap C S) h)
  have : CharZero C := Algebra.charZero_of_charZero R C
  have : CharZero S := Algebra.charZero_of_charZero R S
  have : Module.Finite C S := Module.Finite.of_restrictScalars_finite R C S
  have : Module.Free R C := Module.free_of_finite_type_torsion_free'
  have : Module.Free C S := Module.free_of_finite_type_torsion_free'
  have : FiniteDimensional (FractionRing C) (FractionRing S) :=
    Module.Finite.of_isLocalization C S C⁰
  have hd : differentIdeal R C = ⊤ := differentIdeal_eq_top_of_map_uniformizer hπ hπC
  have hmem := finrank_mul_uniformizer_mem_different
    (FractionRing C) (FractionRing S) hres hπC
  have htower : differentIdeal R S = differentIdeal C S := by
    rw [differentIdeal_eq_differentIdeal_mul_differentIdeal R C S, hd,
      Ideal.map_top, ← Ideal.one_eq_top, mul_one]
  rw [htower, ← Module.finrank_mul_finrank R C S]
  have h := (differentIdeal C S).mul_mem_left (Module.finrank R C : S) hmem
  simpa only [map_mul, map_natCast, Nat.cast_mul,
    ← IsScalarTower.algebraMap_apply R C S, mul_assoc] using h

end IsDiscreteValuationRing
