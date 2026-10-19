/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankStageSectionDetection

/-!
# Rank-stage detection after arbitrary locally Noetherian tests

The original coefficient scheme need not be Noetherian. A locally Noetherian
test scheme has its own base-changed stages, mapping to the original stages.
Vanishing on every original order therefore implies actual vanishing on that
test. This does not assert that these tests detect every arbitrary coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B Y : Scheme.{0}}
  (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (b : B ⟶ S) (v : Y ⟶ B) (m k : ℕ)

/-- Transport the actual ideal-power stage along a coefficient test. -/
def rankStageTestMap :
    rankPullbackThickening E (v ≫ b) m k ⟶ rankPullbackThickening E b m k :=
  pullback.lift (pullback.fst (rankThickeningMap E m k) (v ≫ b))
    (rankPullbackMap E (v ≫ b) m k ≫ v) (by
      rw [Category.assoc]
      exact pullback.condition)

/-- The transported stage retains the original coefficient map. -/
@[reassoc]
theorem rankStageTestMap_projection :
    rankStageTestMap E b v m k ≫ rankPullbackMap E b m k =
      rankPullbackMap E (v ≫ b) m k ≫ v := pullback.lift_snd _ _ _

/-- Original stage vanishing pulls back to the exact same order on every test. -/
theorem rankStageTestMap_zero (a : Γ(B, ⊤))
    (ha : (rankPullbackMap E b m k).appTop a = 0) :
    (rankPullbackMap E (v ≫ b) m k).appTop (v.appTop a) = 0 := by
  change (v.appTop ≫ (rankPullbackMap E (v ≫ b) m k).appTop) a = 0
  rw [← Scheme.Hom.comp_appTop, ← rankStageTestMap_projection,
    Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ha, map_zero]

variable [IsNoetherian S] [IsLocallyNoetherian Y]

/-- All original rank orders detect the coefficient pulled to any locally Noetherian test. -/
theorem test_zero_of_rank_stages (ranks : Set ℕ)
    (hcover : ∀ y : Y, ∃ m ∈ ranks, b (v y) ∈ exactRank E m) (a : Γ(B, ⊤))
    (ha : ∀ m ∈ ranks, ∀ k : ℕ, (rankPullbackMap E b m k).appTop a = 0) :
    v.appTop a = 0 := by
  apply section_zero_of_rank_stages E (v ≫ b) ranks hcover (v.appTop a)
  intro m hm k
  exact rankStageTestMap_zero E b v m k a (ha m hm k)

/-- Equality on all original stages descends on the full test scheme, including nilpotents. -/
theorem test_eq_of_rank_stages (ranks : Set ℕ)
    (hcover : ∀ y : Y, ∃ m ∈ ranks, b (v y) ∈ exactRank E m) (a c : Γ(B, ⊤))
    (hac : ∀ m ∈ ranks, ∀ k : ℕ,
      (rankPullbackMap E b m k).appTop a = (rankPullbackMap E b m k).appTop c) :
    v.appTop a = v.appTop c := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply test_zero_of_rank_stages E b v ranks hcover (a - c)
  intro m hm k
  rw [map_sub, hac m hm k, sub_self]

end FLT.Mazur.RelativeOrderedTuples
