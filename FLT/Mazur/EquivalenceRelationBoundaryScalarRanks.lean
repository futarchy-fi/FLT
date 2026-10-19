/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryMatchingInterior
public import FLT.Mazur.AffineBoundaryScalarNilpotence

/-!
# Scalar neighborhoods and original component ranks

A scalar prime has a matching neighborhood precisely when every minimal
component with a generizing scalar center has matching rank. Failure produces
an actual higher-rank component, retaining its original scalar center.
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
local instance scalarRankOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarRankOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarRankOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "I" => boundaryTestIdeal s κ tests
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ

/-- At every original product point, the full test equations mean matching computed rank. -/
theorem boundaryTestIdeal_le_iff_matching_rank (z : boundaryProduct s κ) :
    I ≤ ((boundaryProduct s κ).isoSpec.hom z).asIdeal ↔ rankOf z = n := by
  rw [boundaryTestIdeal_le_point_iff, ← mem_boundaryTestThickening_range s κ tests 0,
    boundaryTest_range_eq_exactRank, ← boundaryPointRank_eq_iff]

/-- Minimal component containment is precisely matching computed original rank. -/
theorem boundaryTestIdeal_le_component_iff_matching_rank (Q : minimalPrimes C) :
    I ≤ Q.val ↔ rankOf (boundaryComponentPoint s κ Q) = n := by
  have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
      (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) :=
    congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C))
      (boundaryProduct s κ).isoSpec.inv_hom_id
  simpa only [he] using boundaryTestIdeal_le_iff_matching_rank n o U e hU s κ
    (boundaryComponentPoint s κ Q)

/-- A scalar prime is covered exactly when all generizing original components have rank n. -/
theorem mem_boundaryScalarNilpotenceOpen_iff_matching_components (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ tests ↔
      ∀ Q : minimalPrimes C,
        (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal →
          rankOf (boundaryComponentPoint s κ Q) = n := by
  rw [mem_boundaryScalarNilpotenceOpen_iff_components]
  simp_rw [boundaryTestIdeal_le_component_iff_matching_rank n o U e hU s κ]

/-- Exclusion supplies a higher-rank original component whose scalar center generizes the prime. -/
theorem not_mem_boundaryScalarNilpotenceOpen_iff_higher (P : PrimeSpectrum T) :
    P ∉ boundaryScalarNilpotenceOpen s κ tests ↔
      ∃ Q : minimalPrimes C,
        (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal ∧
          n < rankOf (boundaryComponentPoint s κ Q) := by
  rw [mem_boundaryScalarNilpotenceOpen_iff_matching_components n o U e hU s κ]
  push Not
  apply exists_congr
  intro Q
  apply and_congr_right
  intro _
  exact ⟨fun h ↦ lt_of_le_of_ne
    (boundaryExactRank_ge n o U e hU s κ _ _
      (boundaryPointRank_spec n o U e hU s κ _)) (Ne.symm h), fun h ↦ h.ne'⟩

/-- All product points above a certified scalar prime have matching original rank. -/
theorem boundary_rank_matching_of_scalar_mem (z : boundaryProduct s κ)
    (hz : boundaryScalarProjection s κ z ∈ boundaryScalarNilpotenceOpen s κ tests) :
    rankOf z = n := by
  have hm := boundaryScalarNilpotenceOpen_preimage s κ tests hz
  change z ∈ (boundaryNilpotenceOpen s κ tests : Set (boundaryProduct s κ)) at hm
  rw [boundaryNilpotenceOpen_eq_matching_interior n o U e hU s κ] at hm
  exact (boundaryPointRank_eq_iff n o U e hU s κ z n).mpr (interior_subset hm)

/-- The exact scalar obstruction is the closure of the image of higher original ranks. -/
theorem boundaryScalarNilpotenceOpen_compl_eq_higher_image_closure :
    (boundaryScalarNilpotenceOpen s κ tests : Set (PrimeSpectrum T))ᶜ =
      closure (boundaryScalarProjection s κ '' {z : boundaryProduct s κ | n < rankOf z}) := by
  apply Set.Subset.antisymm
  · intro P hP
    obtain ⟨Q, hQ, hr⟩ :=
      (not_mem_boundaryScalarNilpotenceOpen_iff_higher n o U e hU s κ P).mp hP
    have hc : boundaryScalarProjection s κ (boundaryComponentPoint s κ Q) ⤳ P :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hQ
    apply hc.mem_closed isClosed_closure
    exact subset_closure ⟨boundaryComponentPoint s κ Q, hr, rfl⟩
  · apply closure_minimal
    · rintro _ ⟨z, hz, rfl⟩ hm
      exact hz.ne' (boundary_rank_matching_of_scalar_mem n o U e hU s κ z hm)
    · exact (boundaryScalarNilpotenceOpen s κ tests).isOpen.isClosed_compl

attribute [local irreducible] boundaryTestIdeal boundaryScalarHom completeAffineOrbitTests
  boundaryPointRank

/-- Matching generizing components supply one scalar neighborhood and a full power equation. -/
theorem boundary_matching_scalar_denominator (P : PrimeSpectrum T)
    (h : ∀ Q : minimalPrimes C,
      (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal →
        rankOf (boundaryComponentPoint s κ Q) = n) :
    ∃ (order : ℕ) (t : T), t ∉ P.asIdeal ∧
      boundaryScalarHom s κ t ∈ (I ^ order).annihilator ∧
      ((I).map (algebraMap C (Localization.Away (boundaryScalarHom s κ t)))) ^ order = ⊥ := by
  apply ScalarLocalizedIdealNilpotence.exists_scalar_neighborhood
    (boundaryScalarHom s κ) I P.asIdeal (boundaryTestIdeal_fg s κ tests)
  intro Q hQ
  apply (boundaryTestIdeal_le_component_iff_matching_rank n o U e hU s κ Q).mpr
  apply h Q
  rwa [boundaryScalarHom_comap_component] at hQ

end FLT.Mazur.EquivalenceRelationNormalizedFrames
