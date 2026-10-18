/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeExactRankFactorization

/-!
# Recovery of exact-rank coefficients at a finite original stage

A sufficiently high original rank stage recovers a compact exact-rank
coefficient scheme by an isomorphism. The stage orders have canonical
transitions, so this assertion concerns the full scheme and not its reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (b : B ⟶ S) (n : ℕ)

instance rankStageMap_mono (k : ℕ) : Mono (rankThickeningMap E n k) := by
  unfold rankThickeningMap
  infer_instance

instance rankStagePullbackMap_mono (k : ℕ) : Mono (rankPullbackMap E b n k) := by
  unfold rankPullbackMap
  infer_instance

/-- Increase the actual ideal-power order while preserving the original base. -/
def rankStageTransition {k l : ℕ} (h : k ≤ l) :
    rankThickening E n k ⟶ rankThickening E n l :=
  Scheme.IdealSheafData.inclusion (fun _ ↦ Ideal.pow_le_pow_right (Nat.succ_le_succ h))

/-- The transition preserves the complete original stage map. -/
@[reassoc]
theorem rankStageTransition_map {k l : ℕ} (h : k ≤ l) :
    rankStageTransition E n h ≫ rankThickeningMap E n l = rankThickeningMap E n k := by
  unfold rankThickeningMap rankStageTransition
  rw [Scheme.IdealSheafData.inclusion_subschemeι_assoc]

/-- Rank orders form a compatible directed family of actual scheme maps. -/
@[reassoc]
theorem rankStageTransition_comp {k l m : ℕ} (h : k ≤ l) (h' : l ≤ m) :
    rankStageTransition E n h ≫ rankStageTransition E n h' =
      rankStageTransition E n (h.trans h') := by
  apply (cancel_mono (rankThickeningMap E n m)).mp
  rw [Category.assoc, rankStageTransition_map, rankStageTransition_map, rankStageTransition_map]

/-- The transition on the unchanged coefficient base is the original stage base change. -/
def rankStagePullbackTransition {k l : ℕ} (h : k ≤ l) :
    rankPullbackThickening E b n k ⟶ rankPullbackThickening E b n l :=
  pullback.lift (pullback.fst (rankThickeningMap E n k) b ≫ rankStageTransition E n h)
    (rankPullbackMap E b n k) (by
      rw [Category.assoc, rankStageTransition_map]
      exact pullback.condition)

/-- Stage transitions retain every original coefficient. -/
@[reassoc]
theorem rankStagePullbackTransition_map {k l : ℕ} (h : k ≤ l) :
    rankStagePullbackTransition E b n h ≫ rankPullbackMap E b n l =
      rankPullbackMap E b n k := pullback.lift_snd _ _ _

variable [AlgebraicGeometry.IsNoetherian S] [CompactSpace B]

/-- Every compact exact-rank coefficient scheme is recovered at some finite original order. -/
theorem exists_rankPullbackMap_isIso (hb : Set.range b ⊆ exactRank E n) :
    ∃ k : ℕ, IsIso (rankPullbackMap E b n k) := by
  obtain ⟨k, g, hg⟩ := exists_rankPullback_factor E n b (𝟙 B) (by simpa using hb)
  refine ⟨k, ⟨g, ?_, hg⟩⟩
  apply (cancel_mono (rankPullbackMap E b n k)).mp
  rw [Category.assoc, hg, Category.comp_id, Category.id_comp]

/-- Finite-order recovery is exactly the original pointwise rank condition. -/
theorem exactRank_iff_rankPullbackMap_isIso :
    Set.range b ⊆ exactRank E n ↔ ∃ k : ℕ, IsIso (rankPullbackMap E b n k) := by
  refine ⟨exists_rankPullbackMap_isIso E b n, ?_⟩
  rintro ⟨k, hk⟩ _ ⟨x, rfl⟩
  let _ := hk
  obtain ⟨y, rfl⟩ := (rankPullbackMap E b n k).surjective x
  exact rankPullback_endpoint E b n k y

end FLT.Mazur.RelativeOrderedTuples
