/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.RamifiedOrderSequence
public import FLT.LocalClassFieldTheory.UnitHerbrand
public import FLT.LocalClassFieldTheory.HerbrandExact
public import FLT.LocalClassFieldTheory.CyclicIntegerCohomology

/-!
# Herbrand quotient of the multiplicative group of a local field

The normalized valuation sequence and the six-term cardinal identity give
the field-unit Herbrand quotient. Finiteness of integral-unit H¹ comes from
the constructed open exponential subgroup, and Hilbert 90 kills field H¹.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory IsLocalRing

/-- The periodic six-term identity expressed using actual H² and H¹. -/
theorem cyclicSixTerm_group_card {G : Type} [CommGroup G] [Finite G]
    (S : ShortComplex (Rep ℤ G)) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (hS : S.ShortExact) :
    Nat.card (groupCohomology S.X₁ 2) * Nat.card (groupCohomology S.X₃ 2) *
      Nat.card (groupCohomology S.X₂ 1) =
    Nat.card (groupCohomology S.X₂ 2) * Nat.card (groupCohomology S.X₁ 1) *
      Nat.card (groupCohomology S.X₃ 1) := by
  let := Fintype.ofFinite G
  have he (A : Rep ℤ G) := Nat.card_congr
    (cyclicPeriodicGroupEvenIso A g hg 2 (by decide)).toLinearEquiv.toEquiv
  have ho (A : Rep ℤ G) := Nat.card_congr
    (cyclicPeriodicGroupOddIso A g hg 1 (by decide)).toLinearEquiv.toEquiv
  simpa only [he, ho] using cyclicSixTerm_card S g hS

/-- Finite Hilbert 90 gives cardinality one for field-unit H¹. -/
theorem fieldUnit_H1_card (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) = 1 :=
  Nat.card_unique

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
/-- Normalized valuation and integral-unit Herbrand one give h(Lˣ) = [L:K]. -/
theorem ramifiedField_herbrand_eq_degree :
    (Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) : ℚ) /
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) =
        Module.finrank K L := by
  let : IsCyclic Gal(L/K) := ⟨⟨g, hg⟩⟩
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  have h := cyclicSixTerm_group_card (ramifiedOrderSequence R S K L) g hg
    (ramifiedOrderSequence_shortExact R S K L)
  change Nat.card (groupCohomology (integralUnitRep R S K L) 2) *
    Nat.card (groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 2) *
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1) =
    Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) *
    Nat.card (groupCohomology (integralUnitRep R S K L) 1) *
    Nat.card (groupCohomology (Rep.trivial ℤ Gal(L/K) ℤ) 1) at h
  rw [integralUnit_H2_card_eq_H1 R S K L p g hg,
    trivialInteger_H2_card _ g hg, trivialInteger_H1_card _ g hg,
    fieldUnit_H1_card, mul_one, mul_one, mul_comm] at h
  let := integralUnit_H1_finite R S K L p g hg
  have hc := Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  rw [fieldUnit_H1_card, Nat.cast_one, div_one, ← hc,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

end LocalClassFieldTheory
