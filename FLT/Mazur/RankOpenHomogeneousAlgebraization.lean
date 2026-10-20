/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankOpenCompatibleAlgebraization

/-!
# Homogeneous algebraization on the original rank-image open

Algebraization of a compatible full invariant tower preserves the entire
pulled original boundary ideal. A vanished rank-ideal power supplies the
isomorphism; absence of larger frames proves such a power exists. Extension
across the rank-image complement is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance openBoundaryOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance openBoundaryOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance openBoundaryOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (J : A.IdealSheafData)
local notation "B" => J.comap (Scheme.Opens.ι (rankImageOpen (Over.mk p) n))
local notation "R" => compatibleFunctions (rankOpenFirst (p := p) n) (rankOpenSecond e n)

attribute [local irreducible] rankImageOpen rankStratumIdeal rankStageInvariantTransition
  rankOpenFirst rankOpenSecond

/-- Algebraization through a vanished rank-ideal power preserves the full original boundary. -/
theorem exists_rankOpen_homogeneous_of_power_zero (K : ℕ)
    (hK : rankStratumIdeal (Over.mk p) n ^ (K + 1) = ⊥)
    (w : rankStageCompatibleInvariants e n)
    (hw : ∀ k, w.val k ∈ rankStageGlobalBoundaryKernel e n J k) :
    ∃ z : R, (B).subschemeι.appTop z.val = 0 ∧ rankOpenCompatibleRestriction e n z = w := by
  obtain ⟨z, hz⟩ := (rankOpenCompatibleRestriction_bijective_of_power_zero e n K hK).2 w
  refine ⟨z, ?_, hz⟩
  let j := (rankStratumIdeal (Over.mk p) n ^ (K + 1)).subschemeι
  let _ : IsIso j := (Scheme.isIso_subschemeι_iff_eq_bot
    (rankStratumIdeal (Over.mk p) n ^ (K + 1))).mpr hK
  have hB : (B).comap j = rankStageBoundaryIdeal (p := p) n K J := by
    rw [← Scheme.IdealSheafData.comap_comp]
    rfl
  apply (IdealSheafClosedTransitions.section_zero_iff_of_isIso _ _ j hB z.val).mp
  have hzK : rankOpenInvariantRestriction e n K z = w.val K :=
    congrArg (fun v : rankStageCompatibleInvariants e n ↦ v.val K) hz
  change (rankStageBoundaryIdeal (p := p) n K J).subschemeι.appTop
    (rankOpenInvariantRestriction e n K z).val = 0
  rw [hzK]
  exact hw K

/-- Top-rank homogeneous towers have full original rank-open representatives. -/
theorem exists_rankOpen_homogeneous_of_next_empty [CompactSpace A]
    (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥)
    (w : rankStageCompatibleInvariants e n)
    (hw : ∀ k, w.val k ∈ rankStageGlobalBoundaryKernel e n J k) :
    ∃ z : R, (B).subschemeι.appTop z.val = 0 ∧ rankOpenCompatibleRestriction e n z = w := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_power_eq_bot_of_next_empty (Over.mk p) n hn
  exact exists_rankOpen_homogeneous_of_power_zero e n J K hK w hw

end FLT.Mazur.EquivalenceRelationOrderedFrames
