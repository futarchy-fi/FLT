/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.PeuUnitAnnihilator
public import FLT.GroupScheme.PrimeUnitSubspace

/-!
# The independent prime unit subspace is the unramified cup annihilator

This identifies the existing valuation-unit subspace with the existing
peu-ramification predicate, using the arithmetic calculation on parameters.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing KummerTheory GaloisRepresentation.Extensions

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (K C : Type) [Field K] [Field C] [IsAlgClosed C] [Algebra K C]
  [Algebra.IsSeparable K C] [CharZero C] (A : ValuationSubring K)
  [IsDiscreteValuationRing A] [Finite (ResidueField A)]
  [IsAdicComplete (maximalIdeal A) A] (q : ℕ) [Fact q.Prime]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p]

include p in
/-- The arithmetic annihilator is the independently defined prime unit subspace. -/
theorem isPeuRamifiedClass_iff_primeUnitSubspace
    (x : LinearContinuousClass (ZMod q) Gal(C/K) (RootModule C q)) :
    IsPeuRamifiedClass (k := ZMod q) (unramifiedRestriction A K C).ker
      (linearClassEquiv x) ↔
      x ∈ primeUnitSubspace (exists_unit_root (K := K) (L := C) (n := q)) A := by
  let roots := exists_unit_root (K := K) (L := C) (n := q)
  obtain ⟨y, rfl⟩ := (linearKummerEquiv roots).surjective x
  change IsPeuRamifiedClass (k := ZMod q) (unramifiedRestriction A K C).ker
    (linearClassEquiv (linearKummerMap roots y.toMul)) ↔
      linearKummerMap roots y.toMul ∈ primeUnitSubspace roots A
  rw [linearKummer_mem_primeUnitSubspace_iff, linearKummerMap, Equiv.apply_symm_apply]
  induction y using Quotient.inductionOn with | h a =>
    change IsPeuRamifiedClass (k := ZMod q) (unramifiedRestriction A K C).ker
      (kummerClassMap roots (powerClassMap q a)) ↔ IsUnitClass A q (powerClassMap q a)
    rw [isPeuRamified_parameter_iff_unit_power A K C q p, isUnitClass_iff]
    rfl

end LocalClassFieldTheory
