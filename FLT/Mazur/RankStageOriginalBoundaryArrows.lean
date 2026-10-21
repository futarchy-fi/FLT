/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RankStageCoreRelationPullback

/-!
# Full rank-core boundary arrows in the original boundary relation

Each entire finite-stage boundary relation maps to the unchanged original
boundary relation. Both endpoint identities hold as scheme morphisms, so
they apply to residue-field tests and to nonreduced test schemes alike.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance boundaryArrowOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundaryArrowOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance boundaryArrowOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q) (k : ℕ)
set_option quotPrecheck false
local notation "C" => rankStageCore e n a ha k
local notation "r" => (rankStageFirst (p := p) n k).resLE C _ le_rfl
local notation "s" => (rankStageSecond e n k).resLE C _
  (rankStageCore_invariant e n a ha k).le
local notation "I" => rankStageCoreBoundaryIdeal e n a ha J k
local notation "hI" => rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k
local notation "rI" => pullback.snd r (I).subschemeι
local notation "sI" => InvariantIdealRelation.snd I r s hI
local notation "g" => rankStageCoreOriginalBoundaryMap e n a ha J k
local notation "δ" => rankStageCoreOriginalArrow e n a ha k

/-- The entire stage boundary relation has an actual original-boundary arrow map. -/
def rankStageOriginalBoundaryArrow : pullback r (I).subschemeι ⟶ pullback p J.subschemeι :=
  pullback.lift (pullback.fst r (I).subschemeι ≫ δ) (rI ≫ g) (by
    rw [Category.assoc, rankStageCoreOriginalArrow_first, ← Category.assoc,
      pullback.condition, Category.assoc, Category.assoc]
    congr 1
    exact (IdealSheafClosedTransitions.map_inclusion _ _ _ _).symm)

/-- The first original boundary endpoint is retained exactly. -/
@[reassoc]
theorem rankStageOriginalBoundaryArrow_first :
    rankStageOriginalBoundaryArrow e n a ha J k ≫ pullback.snd p J.subschemeι = rI ≫ g :=
  pullback.lift_snd _ _ _

include hJ in
/-- The independent second endpoint uses the same unchanged original boundary map. -/
@[reassoc]
theorem rankStageOriginalBoundaryArrow_second :
    rankStageOriginalBoundaryArrow e n a ha J k ≫ InvariantIdealRelation.snd J p q hJ =
      sI ≫ g := by
  apply (cancel_mono J.subschemeι).mp
  rw [Category.assoc, InvariantIdealRelation.snd_ι,
    rankStageOriginalBoundaryArrow, pullback.lift_fst_assoc,
    Category.assoc, rankStageCoreOriginalArrow_second]
  rw [Category.assoc, rankStageCoreOriginalBoundaryMap,
    IdealSheafClosedTransitions.map_inclusion, InvariantIdealRelation.snd_ι_assoc]

include hJ in
/-- A stage arrow with prescribed endpoints supplies both original boundary endpoints. -/
theorem rankStage_original_boundary_arrow_of_stage {T : Scheme.{0}}
    (x y : T ⟶ (I).subscheme) (d : T ⟶ pullback r (I).subschemeι)
    (hx : d ≫ rI = x) (hy : d ≫ sI = y) :
    ∃ z : T ⟶ pullback p J.subschemeι,
      z ≫ pullback.snd p J.subschemeι = x ≫ g ∧
      z ≫ InvariantIdealRelation.snd J p q hJ = y ≫ g := by
  refine ⟨d ≫ rankStageOriginalBoundaryArrow e n a ha J k, ?_, ?_⟩
  · rw [Category.assoc, rankStageOriginalBoundaryArrow_first, ← Category.assoc, hx]
  · rw [Category.assoc, rankStageOriginalBoundaryArrow_second, ← Category.assoc, hy]

end FLT.Mazur.EquivalenceRelationOrderedFrames
