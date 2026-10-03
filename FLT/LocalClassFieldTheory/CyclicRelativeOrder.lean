/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RamifiedFieldHerbrand
public import FLT.LocalClassFieldTheory.FiniteContinuousComparison
public import FLT.LocalClassFieldTheory.GaloisInflationH2

/-!
# The order of cyclic relative multiplicative H²

Hilbert 90 turns the proved Herbrand quotient into the actual degree order.
The finite continuous comparison transfers this result to relative classes.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing CategoryTheory

variable (R S K L : Type)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Algebra R S] [Module.Finite R S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R S L]
  [FiniteDimensional K L] [IsGalois K L] [CharZero L]
  [IsAdicComplete (maximalIdeal S) S]
  (p : ℕ) [Fact p.Prime] [CharP (ResidueField S) p]

variable [IsIntegralClosure S R L] [Finite (ResidueField S)]

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

include R S p hg in
/-- Cyclic relative multiplicative H² has exactly the extension degree many elements. -/
theorem cyclicRelative_H2_card :
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Module.finrank K L := by
  have h := ramifiedField_herbrand_eq_degree R S K L p g hg
  rw [fieldUnit_H1_card, Nat.cast_one, div_one] at h
  exact_mod_cast h

include R S p hg in
/-- Finiteness follows from the proved positive order, without a finiteness premise. -/
theorem cyclicRelative_H2_finite : Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  apply Nat.finite_of_card_ne_zero
  rw [cyclicRelative_H2_card R S K L p g hg]
  exact Module.finrank_pos.ne'

attribute [local instance] fieldUnitAction

variable [TopologicalSpace (Additive Lˣ)] [DiscreteTopology (Additive Lˣ)]

include R S p hg in
/-- The actual continuous relative H² has the same degree order. -/
theorem cyclicRelative_continuousH2_card :
    Nat.card (continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2) = Module.finrank K L := by
  rw [Nat.card_congr
    (finiteContinuousCohomologyIso ℤ Gal(L/K) (Additive Lˣ) 2).toLinearEquiv.toEquiv]
  exact cyclicRelative_H2_card R S K L p g hg

include R S p hg in
/-- Continuous cyclic relative H² is finite as a consequence of its degree order. -/
theorem cyclicRelative_continuousH2_finite :
    Finite (continuousCohomology ℤ Gal(L/K) (Additive Lˣ) 2) := by
  apply Nat.finite_of_card_ne_zero
  rw [cyclicRelative_continuousH2_card R S K L p g hg]
  exact Module.finrank_pos.ne'

end LocalClassFieldTheory
