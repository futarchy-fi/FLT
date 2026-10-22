/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeDoubleRankDetection
public import FLT.Mazur.RelativeRankStageTestDetection

/-!
# Independent rank detection on arbitrary locally Noetherian tests

Transport both original ideal-power stages along a coefficient test. Detection
therefore works on every locally Noetherian test without assuming that the
original scalar kernel pair itself is Noetherian.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S B T : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  (x y : B ⟶ S) (v : T ⟶ B) (n m r s : ℕ)

/-- The full iterated stage on a test maps to the original stage at the same two orders. -/
def doubleRankTestMap : doubleRankThickening E (v ≫ x) (v ≫ y) n m r s ⟶
    doubleRankThickening E x y n m r s :=
  pullback.lift
    (pullback.fst (rankThickeningMap E m s) (rankPullbackMap E (v ≫ x) n r ≫ v ≫ y))
    (rankPullbackMap E (rankPullbackMap E (v ≫ x) n r ≫ v ≫ y) m s ≫
      rankStageTestMap E x v n r) (by
        rw [Category.assoc, ← Category.assoc (rankStageTestMap E x v n r),
          rankStageTestMap_projection, Category.assoc]
        exact pullback.condition)

/-- Both-stage transport preserves the exact original coefficient morphism. -/
@[reassoc] theorem doubleRankTestMap_projection :
    doubleRankTestMap E x y v n m r s ≫ doubleRankMap E x y n m r s =
      doubleRankMap E (v ≫ x) (v ≫ y) n m r s ≫ v := by
  have h : doubleRankTestMap E x y v n m r s ≫
      rankPullbackMap E (rankPullbackMap E x n r ≫ y) m s =
      rankPullbackMap E (rankPullbackMap E (v ≫ x) n r ≫ v ≫ y) m s ≫
        rankStageTestMap E x v n r := pullback.lift_snd _ _ _
  rw [doubleRankMap, doubleRankMap, ← Category.assoc, h, Category.assoc,
    rankStageTestMap_projection]
  exact (Category.assoc _ _ _).symm

/-- Stagewise equality pulls back to the same independent rank orders of the test. -/
theorem doubleRankTestMap_eq (a b : Γ(B, ⊤))
    (h : (doubleRankMap E x y n m r s).appTop a =
      (doubleRankMap E x y n m r s).appTop b) :
    (doubleRankMap E (v ≫ x) (v ≫ y) n m r s).appTop (v.appTop a) =
      (doubleRankMap E (v ≫ x) (v ≫ y) n m r s).appTop (v.appTop b) := by
  change (v.appTop ≫ (doubleRankMap E (v ≫ x) (v ≫ y) n m r s).appTop) a =
    (v.appTop ≫ (doubleRankMap E (v ≫ x) (v ≫ y) n m r s).appTop) b
  rw [← Scheme.Hom.comp_appTop, ← doubleRankTestMap_projection,
    Scheme.Hom.comp_appTop]
  exact congrArg (fun c ↦ (doubleRankTestMap E x y v n m r s).appTop c) h

variable [IsNoetherian S] [QuasiCompact E.hom] [IsLocallyNoetherian T]

/-- Original two-rank equations detect the entire locally Noetherian test, with nilpotents. -/
theorem test_eq_of_doubleRank_stages (a b : Γ(B, ⊤))
    (h : ∀ n m r s : ℕ, (doubleRankMap E x y n m r s).appTop a =
      (doubleRankMap E x y n m r s).appTop b) : v.appTop a = v.appTop b := by
  apply (section_eq_iff_doubleRank_stages E (v ≫ x) (v ≫ y) _ _).mpr
  intro n m r s
  exact doubleRankTestMap_eq E x y v n m r s a b (h n m r s)

end FLT.Mazur.RelativeOrderedTuples
