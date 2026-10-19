/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryScalarRanks
public import FLT.Mazur.ScalarComponentRankCeiling
public import FLT.Mazur.RelativeFrameSpecializationCeiling

/-!
# Maximal residual component ranks at original scalar primes

The entire original product has bounded rank. At each scalar prime the
largest relevant component rank is attained whenever it exceeds the frame
size. The component retains its scalar center, and that center has exactly
the same maximal rank bound. No scalar fiber nonemptiness is assumed.
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
local instance scalarCeilingOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarCeilingOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarCeilingOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable [TopologicalSpace.NoetherianSpace A]
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "rankOf" => boundaryPointRank n o U e hU s κ
local notation "center" => fun Q : minimalPrimes C ↦
  boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)
local notation "ranks" => fun Q : minimalPrimes C ↦ rankOf (boundaryComponentPoint s κ Q)

/-- All original component ranks obey one bound derived from the original relation. -/
theorem boundary_component_ranks_bounded : ∃ N : ℕ, ∀ Q : minimalPrimes C, ranks Q ≤ N := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound (Over.mk p)
  refine ⟨N, fun Q ↦ ?_⟩
  obtain ⟨x, hx⟩ := chartBoundaryProduct_surjective n o U e hU s κ
    (boundaryComponentPoint s κ Q)
  have hr := boundaryPointRank_spec n o U e hU s κ (boundaryComponentPoint s κ Q)
  rw [← hx] at hr
  change x ∈ π ⁻¹' boundaryExactRank n o U e hU s κ (rankOf (π x)) at hr
  rw [boundaryExactRank_preimage] at hr
  simpa only [hx] using hN (b x) _ hr.1

/-- The least bound on the frame size and all components with generizing scalar centers. -/
def boundaryScalarRankCeiling (P : PrimeSpectrum T) : ℕ :=
  ScalarComponentRank.ceiling center ranks n
    (boundary_component_ranks_bounded n o U e hU s κ) P

local notation "ceiling" => boundaryScalarRankCeiling n o U e hU s κ
local notation "bounded" => boundary_component_ranks_bounded n o U e hU s κ

/-- The frame size remains a lower bound even when the scalar fiber is empty. -/
theorem boundaryScalarRankCeiling_ge (P : PrimeSpectrum T) : n ≤ ceiling P :=
  ScalarComponentRank.base_le center ranks n bounded P

/-- Every component with scalar center below P is bounded by the constructed original ceiling. -/
theorem boundary_component_rank_le_scalarCeiling (P : PrimeSpectrum T) (Q : minimalPrimes C)
    (hQ : (center Q).asIdeal ≤ P.asIdeal) : ranks Q ≤ ceiling P :=
  ScalarComponentRank.rank_le center ranks n bounded P Q hQ

/-- The original scalar ceiling is monotone under specialization. -/
theorem boundaryScalarRankCeiling_monotone : Monotone ceiling :=
  ScalarComponentRank.monotone center ranks n bounded

/-- A strict rank excess has a maximal original component at its own unchanged scalar center. -/
theorem boundaryScalarRankCeiling_attained (P : PrimeSpectrum T) (hP : n < ceiling P) :
    ∃ Q : minimalPrimes C, (center Q).asIdeal ≤ P.asIdeal ∧
      ranks Q = ceiling P ∧ ceiling (center Q) = ceiling P :=
  ScalarComponentRank.attained_at_own_center center ranks n bounded P hP

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU

/-- The maximal relevant rank equals the frame size precisely on the genuine scalar open. -/
theorem mem_boundaryScalarNilpotenceOpen_iff_ceiling (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ tests ↔ ceiling P = n := by
  rw [mem_boundaryScalarNilpotenceOpen_iff_matching_components n o U e hU s κ]
  constructor
  · intro h
    apply Nat.le_antisymm _ (boundaryScalarRankCeiling_ge n o U e hU s κ P)
    exact ScalarComponentRank.minimal center ranks n bounded P n le_rfl
      (fun Q hQ ↦ (h Q hQ).le)
  · intro h Q hQ
    apply Nat.le_antisymm
    · exact (boundary_component_rank_le_scalarCeiling n o U e hU s κ P Q hQ).trans h.le
    · exact boundaryExactRank_ge n o U e hU s κ _ _
        (boundaryPointRank_spec n o U e hU s κ _)

/-- Every excluded scalar prime supplies a maximal higher component, not an arbitrary witness. -/
theorem boundary_scalar_obstruction_maximal_component (P : PrimeSpectrum T)
    (hP : P ∉ boundaryScalarNilpotenceOpen s κ tests) :
    ∃ Q : minimalPrimes C, (center Q).asIdeal ≤ P.asIdeal ∧
      n < ranks Q ∧ ranks Q = ceiling P ∧ ceiling (center Q) = ceiling P := by
  have hlt : n < ceiling P := lt_of_le_of_ne
    (boundaryScalarRankCeiling_ge n o U e hU s κ P)
    (Ne.symm fun h ↦ hP ((mem_boundaryScalarNilpotenceOpen_iff_ceiling
      n o U e hU s κ P).mpr h))
  obtain ⟨Q, hQ, hr, hc⟩ := boundaryScalarRankCeiling_attained n o U e hU s κ P hlt
  exact ⟨Q, hQ, hr ▸ hlt, hr, hc⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
