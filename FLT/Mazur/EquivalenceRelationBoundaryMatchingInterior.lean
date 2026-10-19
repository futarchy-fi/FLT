/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryComponentBounds
public import FLT.Mazur.AffineBoundaryNilpotenceOpen

/-!
# Matching-rank neighborhoods of original minimal components

The actual nilpotence open is the interior of the matching-rank piece. Its
closed complement is the closure of the higher-rank locus. Matching minimal
components have explicit original denominators and exact local power equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local instance matchingInteriorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance matchingInteriorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance matchingInteriorOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "I" => boundaryTestIdeal s κ tests
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ

/-- Each finite test order has exactly the original matching-rank piece as its support. -/
theorem boundaryTest_range_eq_exactRank (k : ℕ) :
    Set.range (boundaryTestThickeningMap s κ tests k) =
      boundaryExactRank n o U e hU s κ n := by
  rw [← boundaryRankProductMap_range n o U e hU s κ 0 n,
    boundaryRank_matching_range]
  ext z
  rw [mem_boundaryTestThickening_range]
  exact (mem_closedOrbitImage_iff_tests ρ Z (completeChart_isClosed (Fin n) o U) _).symm

/-- The actual open of full local nilpotence is the interior of matching original rank. -/
theorem boundaryNilpotenceOpen_eq_matching_interior :
    (boundaryNilpotenceOpen s κ tests : Set (boundaryProduct s κ)) =
      interior (boundaryExactRank n o U e hU s κ n) := by
  rw [boundaryNilpotenceOpen_eq_interior s κ tests 0, boundaryTest_range_eq_exactRank]

/-- The residual closed set consists precisely of limits of higher original ranks. -/
theorem boundaryNilpotenceOpen_compl_eq_higher_closure :
    (boundaryNilpotenceOpen s κ tests : Set (boundaryProduct s κ))ᶜ =
      closure {z : boundaryProduct s κ | n < rankOf z} := by
  rw [boundaryNilpotenceOpen_compl s κ tests 0, boundaryTest_range_eq_exactRank]
  congr 1
  ext z
  change (z ∉ boundaryExactRank n o U e hU s κ n) ↔ n < rankOf z
  rw [← boundaryPointRank_eq_iff]
  exact ⟨fun h ↦ lt_of_le_of_ne
    (boundaryExactRank_ge n o U e hU s κ _ z (boundaryPointRank_spec n o U e hU s κ z))
    (Ne.symm h), fun h ↦ h.ne'⟩

/-- At an actual minimal component, matching rank already gives an open nilpotence neighborhood. -/
theorem boundaryComponent_mem_matching_nilpotenceOpen
    (Q : minimalPrimes C) :
    boundaryComponentPoint s κ Q ∈ boundaryNilpotenceOpen s κ tests ↔
      rankOf (boundaryComponentPoint s κ Q) = n := by
  rw [boundaryComponent_mem_nilpotenceOpen, boundaryGenericTestIdeal_nilpotent_iff]
  simp_rw [← Ideal.Quotient.eq_zero_iff_mem, boundaryComponent_equation_iff]
  rw [← mem_boundaryTestThickening_range s κ tests 0,
    boundaryTest_range_eq_exactRank, ← boundaryPointRank_eq_iff]

/-- Matching components yield actual principal coefficient charts with an exact power equation. -/
theorem boundary_matching_component_denominator (Q : minimalPrimes C)
    (hQ : rankOf (boundaryComponentPoint s κ Q) = n) :
    ∃ k : ℕ, ∃ u : C, u ∉ Q.val ∧ u ∈ (I ^ k).annihilator ∧
      ((I).map (algebraMap C (Localization.Away u))) ^ k = ⊥ := by
  have hm := (boundaryComponent_mem_matching_nilpotenceOpen n o U e hU s κ Q).mpr hQ
  have hi := (boundaryComponent_mem_nilpotenceOpen s κ tests Q).mp hm
  let _ := Q.property.1.1
  have hc := (MinimalPrimeLocalizedIdeal.localized_nilpotent_iff
    I (boundaryTestIdeal_fg s κ tests) Q).mp hi
  exact FiniteIdealLocalizationDenominators.exists_minimal_neighborhood
    I (boundaryTestIdeal_fg s κ tests) Q hc

/-- The whole principal neighborhood certified by a power annihilator has matching rank. -/
theorem boundary_rank_eq_of_power_annihilator (k : ℕ) (u : C)
    (hu : u ∈ (I ^ k).annihilator) (z : boundaryProduct s κ)
    (hz : u ∉ ((boundaryProduct s κ).isoSpec.hom z).asIdeal) : rankOf z = n := by
  have hm := (mem_boundaryNilpotenceOpen s κ tests z).mpr ⟨k, u, hz, hu⟩
  change z ∈ (boundaryNilpotenceOpen s κ tests : Set (boundaryProduct s κ)) at hm
  rw [boundaryNilpotenceOpen_eq_matching_interior n o U e hU s κ] at hm
  exact (boundaryPointRank_eq_iff n o U e hU s κ z n).mpr (interior_subset hm)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
