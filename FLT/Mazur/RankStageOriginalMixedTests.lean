/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClosedCoreTests
public import FLT.Mazur.RankStageOriginalAffineEquationErrors

/-!
# Full original mixed tests at every rank order

An original relation arrow constructs a map to the entire rank-stage relation.
The first endpoint uses the actual pulled ideal power, and the second endpoint
square follows from the original relation square without a second kernel choice.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [Etale q] (e : CategoryTheory.EquivalenceRelation p q) (n k : ℕ)
local instance mixedTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance mixedTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
set_option quotPrecheck false
local notation "I" => rankStratumIdeal (Over.mk p) n
attribute [local irreducible] rankStageRelation rankStageFirst rankStageSecond

variable {T : Scheme.{0}} (g g' : T ⟶ (rankImageOpen (Over.mk p) n).toScheme) (δ : T ⟶ D)
  (hδ : δ ≫ p = g ≫ (rankImageOpen (Over.mk p) n).ι)
  (hδ' : δ ≫ q = g' ≫ (rankImageOpen (Over.mk p) n).ι)
local notation "K" => (I).comap g
local notation "s" => IdealSheafAffineTestErrors.pulledMap I (k + 1) g

include hδ in
/-- The original first square supplies the complete rank-stage pullback square. -/
theorem rankStage_mixed_test_square :
    ((K ^ (k + 1)).subschemeι ≫ δ) ≫ p =
      s ≫ rankThickeningMap (Over.mk p) n k := by
  simp only [Category.assoc, hδ, rankThickeningMap,
    IdealSheafAffineTestErrors.pulledMap_inclusion_assoc]

/-- The original arrow lifts to the full rank-stage relation, not a selected branch. -/
def rankStageOriginalMixedTest :
    (K ^ (k + 1)).subscheme ⟶ rankStageRelation (p := p) n k :=
  (rankStageFirst_isPullback (p := p) n k).lift
    ((K ^ (k + 1)).subschemeι ≫ δ) s
    (rankStage_mixed_test_square n k g δ hδ)

/-- The full test keeps the unchanged original arrow. -/
@[reassoc]
theorem rankStageOriginalMixedTest_arrow :
    rankStageOriginalMixedTest n k g δ hδ ≫ rankStageArrow (p := p) n k =
      (K ^ (k + 1)).subschemeι ≫ δ :=
  CategoryTheory.IsPullback.lift_fst _ _ _ _

/-- The first full endpoint is the canonical closed test map. -/
@[reassoc]
theorem rankStageOriginalMixedTest_first :
    rankStageOriginalMixedTest n k g δ hδ ≫ rankStageFirst (p := p) n k = s :=
  CategoryTheory.IsPullback.lift_snd _ _ _ _

variable [QuasiCompact p] [IsLocallyNoetherian A]

include hδ' in
/-- The second full endpoint retains the independent original endpoint. -/
@[reassoc]
theorem rankStageOriginalMixedTest_second :
    rankStageOriginalMixedTest n k g δ hδ ≫ rankStageSecond e n k ≫
      (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g' := by
  apply (cancel_mono (rankImageOpen (Over.mk p) n).ι).mp
  simp only [Category.assoc]
  change rankStageOriginalMixedTest n k g δ hδ ≫ rankStageSecond e n k ≫
    rankThickeningMap (Over.mk p) n k = _
  rw [rankStageSecond_map, rankStageOriginalMixedTest_arrow_assoc, hδ']

end FLT.Mazur.EquivalenceRelationOrderedFrames
