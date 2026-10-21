/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantIdealRelationMonomorphism
public import FLT.Mazur.RankStageOriginalBoundaryArrows

/-!
# Order compatibility of full original boundary arrows

Arrows constructed independently at two finite orders have the same original
boundary arrow whenever their prescribed endpoints are related by the exact
boundary transition. No compatible choice of relation arrows is assumed.
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
local instance arrowCompatOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance arrowCompatOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance arrowCompatOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
set_option quotPrecheck false
local notation "C" k:max => rankStageCore e n a ha k
local notation "r" k:max => (rankStageFirst (p := p) n k).resLE (C k) _ le_rfl
local notation "s" k:max => (rankStageSecond e n k).resLE (C k) _
  (rankStageCore_invariant e n a ha k).le
local notation "I" k:max => rankStageCoreBoundaryIdeal e n a ha J k
local notation "hI" k:max => rankStageCoreBoundaryIdeal_invariant e n a ha J hJ k
local notation "rI" k:max => pullback.snd (r k) (I k).subschemeι
local notation "sI" k:max => InvariantIdealRelation.snd (I k) (r k) (s k) (hI k)

include hJ in
/-- Independent stage arrows coincide in the original relation along exact order transitions. -/
theorem rankStage_original_boundary_arrows_transition {T : Scheme.{0}} {k l : ℕ}
    (h : k ≤ l) (x y : T ⟶ (I k).subscheme)
    (d : T ⟶ pullback (r k) (I k).subschemeι)
    (d' : T ⟶ pullback (r l) (I l).subschemeι)
    (hx : d ≫ rI k = x) (hy : d ≫ sI k = y)
    (hx' : d' ≫ rI l = x ≫ rankStageCoreBoundaryMap e n a ha J h)
    (hy' : d' ≫ sI l = y ≫ rankStageCoreBoundaryMap e n a ha J h) :
    d ≫ rankStageOriginalBoundaryArrow e n a ha J k =
      d' ≫ rankStageOriginalBoundaryArrow e n a ha J l := by
  let _ : JointlyMono₂ p q := e.toJointlyMono₂
  apply JointlyMono₂.right_cancellation (p₁ := pullback.snd p J.subschemeι)
    (p₂ := InvariantIdealRelation.snd J p q hJ)
  · rw [Category.assoc, Category.assoc, rankStageOriginalBoundaryArrow_first,
      rankStageOriginalBoundaryArrow_first, ← Category.assoc, ← Category.assoc, hx, hx',
      Category.assoc, rankStageCoreOriginalBoundaryMap_transition]
  · rw [Category.assoc, Category.assoc, rankStageOriginalBoundaryArrow_second,
      rankStageOriginalBoundaryArrow_second, ← Category.assoc, ← Category.assoc, hy, hy',
      Category.assoc, rankStageCoreOriginalBoundaryMap_transition]

end FLT.Mazur.EquivalenceRelationOrderedFrames
