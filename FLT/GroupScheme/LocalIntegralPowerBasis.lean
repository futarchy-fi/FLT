/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalPointField
public import FLT.Mathlib.RingTheory.DifferentPowerBasis
public import FLT.Mathlib.RingTheory.DiscreteValuationRing.ResidueGenerator
public import Mathlib.NumberTheory.Padics.RingHoms

/-!
# Integral power bases of finite three-adic extensions

The integral closure of `ℤ_[3]` in a finite extension of `ℚ_[3]` is a finite
free DVR algebra with separable residue extension. It consequently has an
integral power basis, and its different is the annihilator of its Kähler
differentials. No ramification or differential-annihilation bound is asserted.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

variable (L : Type*) [Field L] [Algebra ℚ_[3] L] [Algebra ℤ_[3] L]
  [IsScalarTower ℤ_[3] ℚ_[3] L] [FiniteDimensional ℚ_[3] L]

/-- The full ring of integers of a finite three-adic extension has a power basis. -/
theorem nonempty_threeAdicIntegers_powerBasis :
    Nonempty (PowerBasis ℤ_[3] (ThreeAdicIntegers L)) := by
  have : Finite (IsLocalRing.ResidueField ℤ_[3]) :=
    Finite.of_equiv (ZMod 3) PadicInt.residueField.symm.toEquiv
  exact IsLocalRing.nonempty_powerBasis_of_separable_residue

/-- An integral power basis of the full ring of integers of a finite
three-adic extension. -/
def threeAdicIntegersPowerBasis : PowerBasis ℤ_[3] (ThreeAdicIntegers L) :=
  (nonempty_threeAdicIntegers_powerBasis L).some

/-- The different of any finite three-adic extension is the annihilator of
the Kähler differentials of its full ring of integers. -/
theorem threeAdicDifferent_eq_annihilator_kaehlerDifferential :
    differentIdeal ℤ_[3] (ThreeAdicIntegers L) =
      Module.annihilator (ThreeAdicIntegers L)
        (KaehlerDifferential ℤ_[3] (ThreeAdicIntegers L)) :=
  (threeAdicIntegersPowerBasis L).differentIdeal_eq_annihilator_kaehlerDifferential ℚ_[3] L

/-- Membership in the different is equivalent to annihilating the integral
differentials, without a power-basis hypothesis. -/
theorem mem_threeAdicDifferent_iff (b : ThreeAdicIntegers L) :
    b ∈ differentIdeal ℤ_[3] (ThreeAdicIntegers L) ↔
      ∀ ω : KaehlerDifferential ℤ_[3] (ThreeAdicIntegers L), b • ω = 0 :=
  (threeAdicIntegersPowerBasis L).mem_differentIdeal_iff ℚ_[3] L b

end ThreeAdicPlan
