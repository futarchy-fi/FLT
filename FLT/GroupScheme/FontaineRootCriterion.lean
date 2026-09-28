/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FontaineProperty
public import FLT.GroupScheme.LocalIntegralPowerBasis
public import FLT.Mathlib.RingTheory.PowerBasisApproximateRoots
public import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Fontaine's property as an approximate-root criterion

Every finite three-adic extension has an integral power basis. Consequently,
its Fontaine property can be tested on approximate roots of one minimal
polynomial. Integral homomorphisms extend to field embeddings, so the
property agrees with the field-embedding formulation.

The implication from this root criterion to a strict different bound, and
the finite-flat group-scheme estimate establishing the criterion, remain
separate arithmetic statements.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (A : Type) [CommRing A] [Algebra ℤ_[3] A]

/-- A power basis converts Fontaine's property into the implication from an
approximate root to some genuine integral root over every finite extension. -/
theorem fontaineProperty_iff_approximateRoots (pb : PowerBasis ℤ_[3] A) (m : ℚ) :
    FontaineProperty A m ↔
      ∀ (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
        [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E],
        (∃ y : ThreeAdicIntegers E,
          Polynomial.aeval y (minpoly ℤ_[3] pb.gen) ∈ threeAdicValuationIdeal E m) →
        ∃ z : ThreeAdicIntegers E, Polynomial.aeval z (minpoly ℤ_[3] pb.gen) = 0 := by
  constructor
  · intro h E _ _ _ _ _ hy
    exact pb.nonempty_algHom_iff.mp
      (h E ((pb.nonempty_algHom_quotient_iff (threeAdicValuationIdeal E m)).mpr hy))
  · intro h E _ _ _ _ _ hf
    exact pb.nonempty_algHom_iff.mpr
      (h E ((pb.nonempty_algHom_quotient_iff (threeAdicValuationIdeal E m)).mp hf))

variable (L : Type) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]
  (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
  [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E]

omit [FiniteDimensional ℚ_[3] E] in
/-- Existence of an integral algebra homomorphism is equivalent to existence
of an embedding of the fraction fields. -/
theorem nonempty_threeAdicIntegers_algHom_iff :
    Nonempty (ThreeAdicIntegers L →ₐ[ℤ_[3]] ThreeAdicIntegers E) ↔
      Nonempty (L →ₐ[ℚ_[3]] E) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨galLift ℚ_[3] L E f⟩
  · rintro ⟨f⟩
    exact ⟨galRestrict' ℤ_[3] (ThreeAdicIntegers L) (ThreeAdicIntegers E) f⟩

/-- Fontaine's property for full integers is exactly the usual implication
from a quotient map to a field embedding. -/
theorem fontaineProperty_integers_iff (m : ℚ) :
    FontaineProperty (ThreeAdicIntegers L) m ↔
      ∀ (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
        [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E],
        Nonempty (ThreeAdicIntegers L →ₐ[ℤ_[3]]
          ThreeAdicIntegers E ⧸ threeAdicValuationIdeal E m) →
        Nonempty (L →ₐ[ℚ_[3]] E) := by
  constructor
  · intro h E _ _ _ _ _ hf
    exact (nonempty_threeAdicIntegers_algHom_iff L E).mp (h E hf)
  · intro h E _ _ _ _ _ hf
    exact (nonempty_threeAdicIntegers_algHom_iff L E).mpr (h E hf)

/-- No power-basis hypothesis is needed for the approximate-root criterion
of a finite three-adic extension. -/
theorem fontaineProperty_integers_iff_approximateRoots (m : ℚ) :
    FontaineProperty (ThreeAdicIntegers L) m ↔
      ∀ (E : Type) [Field E] [Algebra ℚ_[3] E] [Algebra ℤ_[3] E]
        [IsScalarTower ℤ_[3] ℚ_[3] E] [FiniteDimensional ℚ_[3] E],
        (∃ y : ThreeAdicIntegers E,
          Polynomial.aeval y (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen) ∈
            threeAdicValuationIdeal E m) →
        ∃ z : ThreeAdicIntegers E,
          Polynomial.aeval z (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen) = 0 :=
  fontaineProperty_iff_approximateRoots _ (threeAdicIntegersPowerBasis L) m

/-- A single approximate root in an extension without an embedding disproves
Fontaine's property. This is the obstruction needed for the different estimate. -/
theorem not_fontaineProperty_of_approximateRoot (m : ℚ)
    (y : ThreeAdicIntegers E)
    (hy : Polynomial.aeval y (minpoly ℤ_[3] (threeAdicIntegersPowerBasis L).gen) ∈
      threeAdicValuationIdeal E m) (hLE : ¬ Nonempty (L →ₐ[ℚ_[3]] E)) :
    ¬ FontaineProperty (ThreeAdicIntegers L) m := by
  intro h
  apply hLE
  exact (fontaineProperty_integers_iff L m).mp h E
    (((threeAdicIntegersPowerBasis L).nonempty_algHom_quotient_iff
      (threeAdicValuationIdeal E m)).mpr ⟨y, hy⟩)

end ThreeAdicPlan
