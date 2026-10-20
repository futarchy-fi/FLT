/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageStableTransitions
public import FLT.Mazur.RankStageCompatibleKernelObstruction
public import FLT.Mazur.RankStratumTopNilpotence
public import FLT.Mazur.StableCompatibleRingTower

/-!
# Algebraization on the unchanged original rank-image open

Restriction uses the original full open relation. When a full power of its
rank ideal vanishes, every compatible invariant tower uniquely comes from
an invariant section on that original open. This does not extend it across
the complement of the rank-image open in the original affine source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples SchemeEffectiveEpiSections SchemeRelationInvariantSpectrum
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance openAlgebraOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance openAlgebraOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance openAlgebraOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ)
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "r" => rankOpenFirst (p := p) n
local notation "s" => rankOpenSecond e n

/-- Restrict full invariants of the original rank-image open to an actual closed order. -/
def rankOpenInvariantRestriction (k : ℕ) :
    compatibleFunctions r s →+* rankStageInvariants e n k :=
  relationPullback r s _ _ (I ^ (k + 1)).subschemeι
    (pullback.fst r (I ^ (k + 1)).subschemeι) pullback.condition
    (InvariantIdealRelation.snd_ι _ _ _ _).symm

/-- These restrictions keep all closed-order compatibility equations. -/
theorem rankOpenInvariantRestriction_transition {k l : ℕ} (h : k ≤ l)
    (z : compatibleFunctions r s) :
    rankStageInvariantTransition e n h (rankOpenInvariantRestriction e n l z) =
      rankOpenInvariantRestriction e n k z := by
  apply Subtype.ext
  change (rankStageTransition (Over.mk p) n h ≫ (I ^ (l + 1)).subschemeι).appTop z.val = _
  rw [rankStageTransition, Scheme.IdealSheafData.inclusion_subschemeι]
  rfl

/-- An original full rank-open invariant gives a complete compatible coefficient tower. -/
def rankOpenCompatibleRestriction : compatibleFunctions r s →+*
    rankStageCompatibleInvariants e n where
  toFun z := ⟨fun k ↦ rankOpenInvariantRestriction e n k z,
    fun _ _ h ↦ rankOpenInvariantRestriction_transition e n h z⟩
  map_zero' := Subtype.ext (funext fun k ↦ map_zero (rankOpenInvariantRestriction e n k))
  map_one' := Subtype.ext (funext fun k ↦ map_one (rankOpenInvariantRestriction e n k))
  map_add' z w := Subtype.ext
    (funext fun k ↦ map_add (rankOpenInvariantRestriction e n k) z w)
  map_mul' z w := Subtype.ext
    (funext fun k ↦ map_mul (rankOpenInvariantRestriction e n k) z w)

attribute [local irreducible] rankStageInvariantTransition rankStratumIdeal
  rankImageOpen rankOpenFirst rankOpenSecond

variable (K : ℕ)
  (hK : rankStratumIdeal (Over.mk p) n ^ (K + 1) = ⊥)

include hK in
/-- A vanished full ideal power identifies original open invariants with the stable stage. -/
theorem rankOpenInvariantRestriction_bijective_of_power_zero :
    Function.Bijective (rankOpenInvariantRestriction e n K) := by
  let _ : IsIso (I ^ (K + 1)).subschemeι :=
    (Scheme.isIso_subschemeι_iff_eq_bot (I ^ (K + 1))).mpr hK
  let _ : IsIso (pullback.fst r (I ^ (K + 1)).subschemeι) := inferInstance
  exact relationPullback_bijective_of_isIso _ _ _ _ _ _ _ _

include hK in
/-- Every compatible full tower algebraizes uniquely on the unchanged original rank-image open. -/
theorem rankOpenCompatibleRestriction_bijective_of_power_zero :
    Function.Bijective (rankOpenCompatibleRestriction e n) := by
  have hstable := rankStratum_powers_stable_of_eq_bot (Over.mk p) n K hK
  have he := CompatibleRingTower.stable_eval_bijective
    (fun _ _ h ↦ rankStageInvariantTransition e n h)
    (fun _ _ _ h h' z ↦ DFunLike.congr_fun (rankStageInvariantTransition_comp e n h h') z)
    K (fun l h ↦ rankStageInvariantTransition_bijective_of_power_eq e n h (hstable l h))
  exact (Function.Bijective.of_comp_iff' he (rankOpenCompatibleRestriction e n)).mp
    (rankOpenInvariantRestriction_bijective_of_power_zero e n K hK)

variable [CompactSpace A]

/-- Absence of larger frames proves algebraization, with no supplied finite-order witness. -/
theorem rankOpenCompatibleRestriction_bijective_of_next_empty
    (hn : rankImageOpen (Over.mk p) (n + 1) = ⊥) :
    Function.Bijective (rankOpenCompatibleRestriction e n) := by
  let _ : IsNoetherian A := ⟨⟩
  obtain ⟨K, hK⟩ := exists_rankStratum_power_eq_bot_of_next_empty (Over.mk p) n hn
  exact rankOpenCompatibleRestriction_bijective_of_power_zero e n K hK

end FLT.Mazur.EquivalenceRelationOrderedFrames
