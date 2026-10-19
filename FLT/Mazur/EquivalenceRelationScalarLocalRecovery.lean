/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationScalarLocalStages
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Matching recovery and unavoidable maximal residual stages

The full scalar-local chart has a finite matching recovery exactly on the
original scalar nilpotence open. At an excluded prime, every order of the
maximal higher rank stage is nonempty. Increasing the matching order alone
therefore cannot recover this original scalar-local chart.
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
local instance scalarLocalRecoveryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance scalarLocalRecoveryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance scalarLocalRecoveryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

variable (P : PrimeSpectrum T)
local notation "l" => boundaryScalarLocalMap s κ P
local notation "localProduct" => boundaryScalarLocalProduct s κ P

local notation "δ" => boundaryScalarLocalProjection n o U e hU s κ P
local notation "endpoint" => boundaryScalarLocalEndpoint n o U e hU s κ P
local notation "rankOf" => boundaryPointRank n o U e hU s κ
variable [AlgebraicGeometry.IsNoetherian A]
local notation "ceiling" => boundaryScalarRankCeiling n o U e hU s κ P

/-- A strict scalar rank excess has a nonempty maximal stage at every original ideal-power order. -/
theorem boundaryScalarLocal_maximal_stage_nonempty (k : ℕ) (hP : n < ceiling) :
    Nonempty (rankPullbackThickening (Over.mk p) endpoint ceiling k) := by
  obtain ⟨Q, z, _, hz⟩ := boundaryScalarLocal_maximum_attained n o U e hU s κ P hP
  obtain ⟨x, hx⟩ := (δ).surjective z
  have hr : endpoint x ∈ exactRank (Over.mk p) ceiling := by
    apply (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P x ceiling).mpr
    simpa only [hx] using hz
  have hm : x ∈ Set.range (rankPullbackMap (Over.mk p) endpoint ceiling k) := by
    rw [rankPullbackMap_range]
    exact hr
  obtain ⟨y, _⟩ := hm
  exact ⟨y⟩

variable [TopologicalSpace.NoetherianSpace U.toScheme]
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU

/-- Full scalar-local matching rank is the original scalar nilpotence condition. -/
theorem boundaryScalarLocalEndpoint_matching_iff :
    Set.range endpoint ⊆ exactRank (Over.mk p) n ↔
      P ∈ boundaryScalarNilpotenceOpen s κ tests := by
  rw [← boundaryScalarLocal_matching_iff n o U e hU s κ P]
  constructor
  · intro h z
    obtain ⟨x, hx⟩ := (δ).surjective z
    have hr := (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P x n).mp
      (h (Set.mem_range_self x))
    simpa only [hx] using hr
  · rintro h _ ⟨x, rfl⟩
    exact (boundaryScalarLocalEndpoint_rank_iff n o U e hU s κ P x n).mpr (h (δ x))

/-- A finite matching stage recovers the entire local chart exactly on the genuine scalar open. -/
theorem boundaryScalarLocal_matching_recovery_iff :
    (∃ k : ℕ, IsIso (rankPullbackMap (Over.mk p) endpoint n k)) ↔
      P ∈ boundaryScalarNilpotenceOpen s κ tests := by
  rw [← exactRank_iff_rankPullbackMap_isIso, boundaryScalarLocalEndpoint_matching_iff]

/-- Every matching order fails to recover the full scalar-local chart at an excluded prime. -/
theorem boundaryScalarLocal_matching_not_isIso
    (hP : P ∉ boundaryScalarNilpotenceOpen s κ tests) (k : ℕ) :
    ¬ IsIso (rankPullbackMap (Over.mk p) endpoint n k) :=
  fun hk ↦ hP ((boundaryScalarLocal_matching_recovery_iff n o U e hU s κ P).mp ⟨k, hk⟩)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
