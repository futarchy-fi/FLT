/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointFrameCover

/-!
# Affine source neighborhoods for every original mixed-frame arrow

Refine each constructed common-frame source by its actual affine open cover.
These affine etale neighborhoods still exhaust the full mixed relation and
retain both independent original frames and the unchanged original arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)

/-- Affine patches of all the bounded common-frame sources. -/
def JointAffineIndex :=
  Σ c : JointIndex I J, (jointSource (p := p) (q := q) o c).affineCover.I₀

/-- An actual affine source patch, with its complete original scheme structure. -/
def jointAffineSource (c : JointAffineIndex (p := p) (q := q) (J := J) o) : Scheme :=
  (jointSource (p := p) (q := q) o c.1).affineCover.X c.2

instance jointAffineSource_isAffine (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    IsAffine (jointAffineSource o c) := by
  unfold jointAffineSource
  infer_instance

/-- The open immersion from the affine patch to its entire common frame. -/
def jointAffineInclusion (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    jointAffineSource o c ⟶ jointSource (p := p) (q := q) o c.1 :=
  (jointSource (p := p) (q := q) o c.1).affineCover.f c.2

instance jointAffineInclusion_isOpenImmersion
    (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    IsOpenImmersion (jointAffineInclusion o c) := by
  unfold jointAffineInclusion
  infer_instance

/-- The original mixed relation map of the affine source neighborhood. -/
def jointAffineMap (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    jointAffineSource o c ⟶ relation p q I J o o' :=
  jointAffineInclusion o c ≫ jointMap e o o' c.1

instance jointAffineMap_mono (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    Mono (jointAffineMap e o o' c) := by
  unfold jointAffineMap
  infer_instance

variable [Etale p]

instance jointAffineMap_etale (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    Etale (jointAffineMap e o o' c) := by
  unfold jointAffineMap
  infer_instance

/-- Every point of the entire original relation has one of these affine source neighborhoods. -/
theorem jointAffineMap_covers (x : relation p q I J o o') :
    ∃ (c : JointAffineIndex (p := p) (q := q) (J := J) o)
      (y : jointAffineSource o c), jointAffineMap e o o' c y = x := by
  obtain ⟨c, y, hy⟩ := jointMap_covers e o o' x
  obtain ⟨j, v, hv⟩ := (jointSource (p := p) (q := q) o c).affineCover.exists_eq y
  refine ⟨⟨c, j⟩, v, ?_⟩
  change jointMap e o o' c
    ((jointSource (p := p) (q := q) o c).affineCover.f j v) = x
  rw [hv, hy]

/-- The constructed affine neighborhoods form an actual etale cover of the full relation. -/
def jointAffineCover : (relation p q I J o o').Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers _ (jointAffineSource (p := p) (q := q) (J := J) o)
    (jointAffineMap e o o') (jointAffineMap_covers e o o') (fun _ ↦ inferInstance)

omit [Etale p] in
/-- The affine neighborhoods retain the original relation arrow as a whole scheme morphism. -/
@[reassoc] theorem jointAffineMap_arrow
    (c : JointAffineIndex (p := p) (q := q) (J := J) o) :
    jointAffineMap e o o' c ≫ arrow p q I J o o' =
      jointAffineInclusion o c ≫ coordinate p q (Fin c.1.1.val)
        (c.1.2.val.1 o) (c.1.2.val.2 o') := by
  rw [jointAffineMap, Category.assoc]
  exact congrArg (fun f ↦ jointAffineInclusion o c ≫ f)
    (jointGraph_arrow e o o' c.1.2.val.1 c.1.2.val.2)

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
