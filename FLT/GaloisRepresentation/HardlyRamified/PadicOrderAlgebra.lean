/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.ResidualCharacteristic
public import FLT.Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Localization.Finiteness
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.Topology.Algebra.Module.Compact


/-!
# General-prime order normalization: Algebra

The construction retains the original order and its fraction field.
-/

@[expose] public noncomputable section
namespace PadicOrderPlan
open scoped nonZeroDivisors

variable (p : ℕ) [Fact p.Prime]
variable (R : Type*) [CommRing R] [Algebra ℤ_[p] R] [IsDomain R]
  [Module.Free ℤ_[p] R] [Module.Finite ℤ_[p] R]

/-- The induced p-adic field structure on the fraction field of an order. -/
scoped instance fractionAlgebra : Algebra ℚ_[p] (FractionRing R) :=
  (IsFractionRing.lift (K := ℚ_[p])
    (FaithfulSMul.algebraMap_injective ℤ_[p] (FractionRing R))).toAlgebra

scoped instance fractionScalarTower : IsScalarTower ℤ_[p] ℚ_[p] (FractionRing R) :=
  .of_algebraMap_eq fun x ↦
    (IsFractionRing.lift_algebraMap
      (FaithfulSMul.algebraMap_injective ℤ_[p] (FractionRing R)) x).symm

/-- The fraction field of a finite free p-adic order is finite-dimensional. -/
scoped instance fractionFiniteDimensional : FiniteDimensional ℚ_[p] (FractionRing R) :=
  Module.Finite.of_isLocalization ℤ_[p] R ℤ_[p]⁰

/-- The normalization is the integral closure in the order's own fraction field. -/
abbrev NormalizedOrder := integralClosure ℤ_[p] (FractionRing R)

/-- The normalization is finite over the p-adic integers. -/
theorem normalizedOrder_finite : Module.Finite ℤ_[p] (NormalizedOrder p R) :=
  IsIntegralClosure.finite ℤ_[p] ℚ_[p] (FractionRing R) (NormalizedOrder p R)

/-- The normalization is free over the p-adic integers. -/
theorem normalizedOrder_free : Module.Free ℤ_[p] (NormalizedOrder p R) :=
  IsIntegralClosure.module_free ℤ_[p] ℚ_[p] (FractionRing R) (NormalizedOrder p R)

/-- Normalizing the order does not change its fraction field. -/
theorem normalizedOrder_isFractionRing : IsFractionRing (NormalizedOrder p R) (FractionRing R) :=
  IsIntegralClosure.isFractionRing_of_finite_extension
    ℤ_[p] ℚ_[p] (FractionRing R) (NormalizedOrder p R)

/-- The normalization is a Dedekind domain. -/
theorem normalizedOrder_isDedekindDomain : IsDedekindDomain (NormalizedOrder p R) :=
  IsIntegralClosure.isDedekindDomain ℤ_[p] ℚ_[p] (FractionRing R) (NormalizedOrder p R)

/-- The integral rank agrees with the degree of the fraction field. -/
theorem normalizedOrder_finrank :
    Module.finrank ℤ_[p] (NormalizedOrder p R) = Module.finrank ℚ_[p] (FractionRing R) :=
  IsIntegralClosure.rank ℤ_[p] ℚ_[p] (FractionRing R) (NormalizedOrder p R)

/-- The natural embedding of the original order into its normalization. -/
def toNormalizedOrder : R →ₐ[ℤ_[p]] NormalizedOrder p R :=
  (IsScalarTower.toAlgHom ℤ_[p] R (FractionRing R)).codRestrict _ fun r ↦
    (Algebra.IsIntegral.isIntegral (R := ℤ_[p]) r).map
      (IsScalarTower.toAlgHom ℤ_[p] R (FractionRing R))

omit [IsDomain R] [Module.Free ℤ_[p] R] in
@[simp]
theorem coe_toNormalizedOrder (r : R) :
    (toNormalizedOrder p R r : FractionRing R) = algebraMap R (FractionRing R) r := rfl

omit [IsDomain R] [Module.Free ℤ_[p] R] in
/-- The normalization map is injective. -/
theorem toNormalizedOrder_injective : Function.Injective (toNormalizedOrder p R) := by
  intro x y h
  exact IsFractionRing.injective R (FractionRing R) (congrArg Subtype.val h)

attribute [scoped instance] normalizedOrder_finite normalizedOrder_free
  normalizedOrder_isFractionRing normalizedOrder_isDedekindDomain

end PadicOrderPlan
