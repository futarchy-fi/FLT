/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointFrameCover
public import FLT.Mazur.EquivalenceRelationBoundarySubframeGeometry

/-!
# Exhaustive common-frame comparison on the exact original boundary

The common-frame graphs give Cartesian maps on the full pulled-back boundary,
retaining its ideal and nilpotents. Their finite family covers that entire
boundary, and the original closed arrows are the existing label transitions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J) (i : B ⟶ A)

/-- The entire original mixed relation restricted to the boundary of its first endpoint. -/
def jointBoundaryTarget : Scheme := pullback (fst p q I J o o' ≫ first p q I o) i

/-- The actual ambient inclusion of this boundary relation. -/
def jointBoundaryTargetInclusion :
    jointBoundaryTarget (p := p) (q := q) o o' i ⟶ relation p q I J o o' :=
  pullback.fst _ _

/-- The common-frame source retains its full pulled-back boundary scheme. -/
def jointBoundarySource (c : JointIndex I J) : Scheme :=
  boundary (p := p) (q := q) (Fin c.1.val) (c.2.val.1 o) i

/-- The common-frame comparison on the full, possibly nonreduced boundary. -/
def jointBoundaryMap (c : JointIndex I J) :
    jointBoundarySource (p := p) (q := q) o i c ⟶ jointBoundaryTarget (p := p) (q := q) o o' i :=
  pullback.lift (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ≫
    jointMap e o o' c) (endpoint (Fin c.1.val) (c.2.val.1 o) i) (by
      rw [Category.assoc, show jointMap e o o' c ≫ fst p q I J o o' ≫
        first p q I o = first p q (Fin c.1.val) (c.2.val.1 o) from
          jointGraph_first e o o' c.2.val.1 c.2.val.2, endpoint_condition])

/-- The original ambient relation comparison is retained exactly on the boundary. -/
@[reassoc] theorem jointBoundaryMap_inclusion (c : JointIndex I J) :
    jointBoundaryMap e o o' i c ≫ jointBoundaryTargetInclusion (p := p) (q := q) o o' i =
      InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i ≫ jointMap e o o' c :=
  pullback.lift_fst _ _ _

/-- The square keeps the full original boundary ideal, rather than only its support. -/
theorem jointBoundaryMap_isPullback (c : JointIndex I J) :
    IsPullback (jointBoundaryMap e o o' i c)
      (InvariantBoundary.inclusion (Fin c.1.val) (c.2.val.1 o) i)
      (jointBoundaryTargetInclusion (p := p) (q := q) o o' i) (jointMap e o o' c) := by
  apply IsPullback.of_right
    (h₁₂ := pullback.snd (fst p q I J o o' ≫ first p q I o) i)
    (h₂₂ := fst p q I J o o' ≫ first p q I o)
  · rw [show jointBoundaryMap e o o' i c ≫ pullback.snd _ _ =
      endpoint (Fin c.1.val) (c.2.val.1 o) i from pullback.lift_snd _ _ _]
    rw [show jointMap e o o' c ≫ fst p q I J o o' ≫ first p q I o =
      first p q (Fin c.1.val) (c.2.val.1 o) from
        jointGraph_first e o o' c.2.val.1 c.2.val.2]
    exact (IsPullback.of_hasPullback (first p q (Fin c.1.val) (c.2.val.1 o)) i).flip
  · exact jointBoundaryMap_inclusion e o o' i c
  · exact (IsPullback.of_hasPullback (fst p q I J o o' ≫ first p q I o) i).flip

variable [Etale p]

instance jointBoundaryMap_etale (c : JointIndex I J) : Etale (jointBoundaryMap e o o' i c) :=
  MorphismProperty.of_isPullback (jointBoundaryMap_isPullback e o o' i c).flip
    (inferInstanceAs (Etale (jointMap e o o' c)))

/-- The boundary comparisons cover every original boundary point, without completeness. -/
theorem jointBoundaryMap_covers (x : jointBoundaryTarget (p := p) (q := q) o o' i) :
    ∃ (c : JointIndex I J) (y : jointBoundarySource (p := p) (q := q) o i c),
      jointBoundaryMap e o o' i c y = x := by
  obtain ⟨c, y, hy⟩ := jointMap_covers e o o'
    (jointBoundaryTargetInclusion (p := p) (q := q) o o' i x)
  obtain ⟨w, hw, _⟩ := Scheme.exists_preimage_of_isPullback
    (jointBoundaryMap_isPullback e o o' i c) x y hy.symm
  exact ⟨c, w, hw⟩

/-- An actual finite etale cover of the entire original boundary relation. -/
def jointBoundaryCover :
    (jointBoundaryTarget (p := p) (q := q) o o' i).Cover (Scheme.precoverage @Etale) :=
  Scheme.Cover.mkOfCovers _ (jointBoundarySource (p := p) (q := q) (J := J) o i)
    (jointBoundaryMap e o o' i) (jointBoundaryMap_covers e o o' i) (fun _ ↦ inferInstance)

omit [Etale p] in
/-- Each boundary comparison retains the original closed arrow supplied by its Cartesian square. -/
@[reassoc] theorem jointBoundaryMap_closedArrow {C : Scheme.{0}} (z : C ⟶ D) (r : C ⟶ B)
    (hr : IsPullback z r p i) (c : JointIndex I J) :
    jointBoundaryMap e o o' i c ≫
      jointBoundaryTargetInclusion (p := p) (q := q) o o' i ≫ arrow p q I J o o' =
      labelTransition (q := q) (Fin c.1.val) (c.2.val.1 o) (c.2.val.2 o') i z r hr ≫ z := by
  rw [jointBoundaryMap_inclusion_assoc, jointMap, jointGraph_arrow]
  exact (labelTransition_arrow _ _ _ _ _ _ _).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
