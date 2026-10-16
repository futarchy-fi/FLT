/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationNormalizedSubframe
public import FLT.Mazur.EquivalenceRelationNormalizedFrameComparison
public import FLT.Mazur.RelativeCompleteSubframe

/-!
# Complete first frames compare to arbitrary smaller frames

The whole original arrow transports the complete frame. Every independently
indexed second frame is its unique moving subframe; it need not be complete.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples EquivalenceRelationOrderedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  {K : Type} [Field K] (u : Spec (.of K) ⟶ source p q I o)
  (v : Spec (.of K) ⟶ source p q J o') (hu : Complete I o u)
  (a : Spec (.of K) ⟶ D) (ha : a ≫ p = u ≫ first p q I o)
  (hb : a ≫ q = v ≫ first p q J o')

local instance subcompareOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance subcompareOver_etale : Etale (Over.mk p).hom := ‹Etale p›

/-- The unique embedding matching the arbitrary target frame after whole-fiber transport. -/
def comparisonEmbedding : J ↪ I :=
  completeSubframeEmbedding (Over.mk p) (comparisonFrame e I o u a ha)
    (comparisonFrame_complete e I o u hu a ha) (targetFrame J o' v a hb)

/-- The moving subframe matches the independent second frame as an actual scheme map. -/
theorem comparisonEmbedding_subframe :
    u ≫ subframeMap e o o' (comparisonEmbedding e o o' u v hu a ha hb) = v := by
  apply hom_ext_second p q J o' e
  intro j
  rw [Category.assoc, subframeMap_second]
  have hc := congrArg (fun z : Over.mk (a ≫ q) ⟶ Over.mk p ↦ z.left ≫ q)
    (completeSubframeEmbedding_coordinate (Over.mk p) (comparisonFrame e I o u a ha)
      (comparisonFrame_complete e I o u hu a ha) (targetFrame J o' v a hb) j)
  change (rebaseFrame e I a (frameCast I ha.symm (testFrame I o u)) ≫
    distinctCoordinate (Over.mk p) I (comparisonEmbedding e o o' u v hu a ha hb j)).left ≫
      q = (targetFrame J o' v a hb ≫ distinctCoordinate (Over.mk p) J j).left ≫ q at hc
  rw [rebaseFrame_second] at hc
  simpa only [targetFrame, testFrame, frameCast, framePull, frame,
    Over.homMk_left, Over.comp_left, coordinate, Category.assoc] using hc

include e hu a ha hb in
/-- Every full original arrow from a complete frame determines a unique label embedding. -/
theorem complete_original_arrow_unique_embedding :
    ∃! ι : J ↪ I, u ≫ subframeMap e o o' ι = v := by
  refine ⟨comparisonEmbedding e o o' u v hu a ha hb,
    comparisonEmbedding_subframe e o o' u v hu a ha hb, ?_⟩
  intro ι hι
  exact subframeMap_unique e o o' u ι _
    (hι.trans (comparisonEmbedding_subframe e o o' u v hu a ha hb).symm)

include e hu a ha hb in
/-- An arbitrary second frame cannot exceed the size of the complete first frame. -/
theorem original_arrow_cardinality_le : Fintype.card J ≤ Fintype.card I :=
  Fintype.card_le_of_injective _ (comparisonEmbedding e o o' u v hu a ha hb).injective

end FLT.Mazur.EquivalenceRelationNormalizedFrames
