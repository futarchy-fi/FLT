/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageBoundaryIdeal
public import FLT.Mazur.RelativeRankStageRecovery

/-!
# Full relation transitions between infinitesimal rank orders

The ideal-power inclusions lift to the entire original relation. Both endpoints
commute, and the first-endpoint square is cartesian. The unchanged original
boundary ideal pulls back exactly along every transition.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A]
  (e : CategoryTheory.EquivalenceRelation p q) (n : ℕ)
local instance transitionOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance transitionOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance transitionOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable {k l m : ℕ} (h : k ≤ l)

/-- The order transition on the whole original relation, not a selected component. -/
def rankStageRelationTransition : rankStageRelation (p := p) n k ⟶
    rankStageRelation (p := p) n l :=
  (rankStageFirst_isPullback (p := p) n l).lift (rankStageArrow (p := p) n k)
    (rankStageFirst (p := p) n k ≫ rankStageTransition (Over.mk p) n h) (by
      rw [Category.assoc, rankStageTransition_map]
      exact (rankStageFirst_isPullback (p := p) n k).w)

omit [QuasiCompact p] [IsLocallyNoetherian A] in
/-- Transitions retain the entire original arrow. -/
@[reassoc]
theorem rankStageRelationTransition_arrow : rankStageRelationTransition (p := p) n h ≫
    rankStageArrow (p := p) n l = rankStageArrow (p := p) n k :=
  (rankStageFirst_isPullback (p := p) n l).lift_fst _ _ _

omit [QuasiCompact p] [IsLocallyNoetherian A] in
/-- The first endpoint commutes with the actual ideal-power inclusion. -/
@[reassoc]
theorem rankStageRelationTransition_first : rankStageRelationTransition (p := p) n h ≫
    rankStageFirst (p := p) n l =
      rankStageFirst (p := p) n k ≫ rankStageTransition (Over.mk p) n h :=
  (rankStageFirst_isPullback (p := p) n l).lift_snd _ _ _

/-- The independent second endpoint commutes with the same transition. -/
@[reassoc]
theorem rankStageRelationTransition_second : rankStageRelationTransition (p := p) n h ≫
    rankStageSecond e n l = rankStageSecond e n k ≫ rankStageTransition (Over.mk p) n h := by
  apply (cancel_mono (rankThickeningMap (Over.mk p) n l)).mp
  rw [Category.assoc, rankStageSecond_map, rankStageRelationTransition_arrow_assoc,
    Category.assoc, rankStageTransition_map, rankStageSecond_map]

omit [QuasiCompact p] [IsLocallyNoetherian A] in
/-- The whole first-endpoint relation is preserved by base change between orders. -/
theorem rankStageRelationTransition_isPullback :
    IsPullback (rankStageRelationTransition (p := p) n h) (rankStageFirst (p := p) n k)
      (rankStageFirst (p := p) n l) (rankStageTransition (Over.mk p) n h) := by
  apply IsPullback.of_right _ (rankStageRelationTransition_first n h)
    (rankStageFirst_isPullback (p := p) n l)
  rw [rankStageRelationTransition_arrow, rankStageTransition_map]
  exact rankStageFirst_isPullback (p := p) n k

omit [QuasiCompact p] [IsLocallyNoetherian A] in
/-- Composition of order transitions agrees on the full relation scheme. -/
@[reassoc]
theorem rankStageRelationTransition_comp (h' : l ≤ m) :
    rankStageRelationTransition (p := p) n h ≫ rankStageRelationTransition (p := p) n h' =
      rankStageRelationTransition (p := p) n (h.trans h') := by
  apply (rankStageFirst_isPullback (p := p) n m).hom_ext
  · simp only [Category.assoc, rankStageRelationTransition_arrow]
  · simp only [Category.assoc, rankStageRelationTransition_first,
      rankStageRelationTransition_first_assoc, rankStageTransition_comp]

omit [QuasiCompact p] [IsLocallyNoetherian A] in
/-- Boundary transport is equality of full ideals, including every nilpotent coefficient. -/
theorem rankStageBoundaryIdeal_transition (J : A.IdealSheafData) :
    (rankStageBoundaryIdeal (p := p) n l J).comap (rankStageTransition (Over.mk p) n h) =
      rankStageBoundaryIdeal (p := p) n k J := by
  unfold rankStageBoundaryIdeal
  rw [← Scheme.IdealSheafData.comap_comp, rankStageTransition_map]

end FLT.Mazur.EquivalenceRelationOrderedFrames
