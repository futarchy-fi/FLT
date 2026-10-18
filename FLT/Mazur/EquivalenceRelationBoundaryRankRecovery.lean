/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationBoundaryRankDescent
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Finite-stage recovery of the whole original chart boundary

The original finite test ideal is nilpotent exactly when a finite matching
rank stage is isomorphic to the entire chart boundary. This sharpens pointwise
coverage to recovery of all coefficients, but does not assert the required
nilpotence on residual charts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryCoordinate
  rankPullbackThickening rankPullbackMap
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [TopologicalSpace.NoetherianSpace U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local instance rankRecoveryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance rankRecoveryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance rankRecoveryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local notation "ρ" => restrictedAction (action e (Fin n) o) U hU
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local notation "Z" => U.ι ⁻¹' completePointLocus («p» := p) («q» := q) (Fin n) o
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU

/-- Full-product test nilpotence is exact matching rank on the whole chart boundary. -/
theorem boundaryTestIdeal_nilpotent_iff_chart_exactRank :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔ Set.range b ⊆ exactRank (Over.mk p) n := by
  rw [boundaryTestIdeal_nilpotent_iff_higher_empty n o U e hU s κ 0]
  constructor
  · intro h _ hx
    obtain ⟨x, rfl⟩ := hx
    obtain ⟨m, hm⟩ := exists_exactRank (Over.mk p) (b x)
    have hr : x ∈ Set.range (rankPullbackMap (Over.mk p) b m 0) := by
      rw [rankPullbackMap_range]
      exact hm
    obtain ⟨y, hy⟩ := hr
    have he : m = n := by
      rcases lt_trichotomy m n with hmn | hmn | hmn
      · exact ((boundary_rankThickening_empty_below n o U e hU s κ m 0 hmn).false y).elim
      · exact hmn
      · exact ((h m hmn).false y).elim
    exact he ▸ hm
  · intro h m hmn
    refine ⟨fun y ↦ ?_⟩
    have hn := h (Set.mem_range_self (rankPullbackMap (Over.mk p) b m 0 y))
    have hm := rankPullback_endpoint (Over.mk p) b m 0 y
    exact hn.2 (rankImageOpen_antitone (Over.mk p) hmn hm.1)

variable [AlgebraicGeometry.IsNoetherian A]

/-- Some matching rank order recovers the full chart boundary exactly when the tests vanish. -/
theorem boundaryTestIdeal_nilpotent_iff_rankStage_isIso :
    IsNilpotent (boundaryTestIdeal s κ tests) ↔
      ∃ k : ℕ, IsIso (rankPullbackMap (Over.mk p) b n k) := by
  let _ : CompactSpace (chartBoundary n o U e hU s κ) := by
    unfold chartBoundary
    infer_instance
  rw [boundaryTestIdeal_nilpotent_iff_chart_exactRank]
  exact exactRank_iff_rankPullbackMap_isIso (Over.mk p) b n

/-- A failed test precludes recovery by every finite matching order of the original stage. -/
theorem boundary_rankStage_not_isIso_of_failed_test
    (t : invariantCoordinates ρ) (ht : t ∈ tests)
    (h : ¬ IsNilpotent (boundaryCoordinate s κ t)) (k : ℕ) :
    ¬ IsIso (rankPullbackMap (Over.mk p) b n k) := by
  intro hk
  have hi := (boundaryTestIdeal_nilpotent_iff_rankStage_isIso n o U e hU s κ).mpr ⟨k, hk⟩
  exact h ((boundaryTestIdeal_nilpotent_iff s κ tests).mp hi t ht)

end FLT.Mazur.EquivalenceRelationNormalizedFrames
