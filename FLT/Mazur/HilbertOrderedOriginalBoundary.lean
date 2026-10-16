/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFullRelationOrderedPoints
public import FLT.Mazur.HilbertBoundaryRelationTests
public import FLT.Mazur.FiniteGroupPullbackAction

/-!
# The original closed boundary on ordered full-relation tests

Pull back the actual original closed boundary, retaining its ideal and nilpotents.
The ordered-point action lifts to this exact scheme pullback. Every coordinate
lands in the entire original closed relation with both endpoint maps preserved.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "C" => originalClosedRelation f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
variable (n : ℕ)
local notation "F" => fullRelationOrderedPoints f hL d V c k n
local notation "ρ" => fullRelationOrderedAction f hL d V c k n
local notation "hρ" => fullRelationOrderedAction_first f hL d V c k n
local notation "E" => fullRelationOverFirst f hL d V c k
open RelativeOrderedTuples

/-- The exact original closed boundary, pulled back to the full ordered-point scheme. -/
def orderedOriginalBoundary : Scheme := pullback (F).hom (i).left

/-- Its actual inclusion retains the original boundary ideal scheme-theoretically. -/
def orderedOriginalBoundaryInclusion : orderedOriginalBoundary f hL d V c k n ⟶ (F).left :=
  pullback.fst (F).hom (i).left

instance orderedOriginalBoundaryInclusion_closed :
    IsClosedImmersion (orderedOriginalBoundaryInclusion f hL d V c k n) :=
  inferInstanceAs (IsClosedImmersion (pullback.fst (F).hom (i).left))

/-- The actual action on the unchanged scheme boundary. -/
def orderedOriginalBoundaryAction :
    Equiv.Perm (Fin n) →* Aut (orderedOriginalBoundary f hL d V c k n) :=
  FiniteGroupPullback.action ρ (F).hom hρ (i).left

omit [Etale V.hom] in
/-- The original closed inclusion is equivariant for the constructed boundary action. -/
@[reassoc] theorem orderedOriginalBoundary_equivariant (e : Equiv.Perm (Fin n)) :
    (orderedOriginalBoundaryAction f hL d V c k n e).hom ≫
      orderedOriginalBoundaryInclusion f hL d V c k n =
        orderedOriginalBoundaryInclusion f hL d V c k n ≫ (ρ e).hom :=
  FiniteGroupPullback.action_fst ρ (F).hom hρ (i).left e

/-- Every ordered boundary arrow lifts into the entire original closed relation. -/
def orderedOriginalBoundaryCoordinate (j : Fin n) :
    orderedOriginalBoundary f hL d V c k n ⟶ (C).left :=
  (originalClosedFst_isPullback f hL d V c k).lift
    (pullback.fst (F).hom (i).left ≫ (distinctCoordinate E (Fin n) j).left)
    (pullback.snd (F).hom (i).left) (by
      rw [Category.assoc, fullRelationOrdered_first, pullback.condition])

omit [Etale V.hom] in
/-- No original relation arrow is changed by the closed-coordinate construction. -/
@[reassoc] theorem orderedOriginalBoundaryCoordinate_arrow (j : Fin n) :
    orderedOriginalBoundaryCoordinate f hL d V c k n j ≫ (z).left =
      orderedOriginalBoundaryInclusion f hL d V c k n ≫
        (distinctCoordinate E (Fin n) j).left :=
  (originalClosedFst_isPullback f hL d V c k).lift_fst _ _ _

omit [Etale V.hom] in
/-- Every coordinate retains the original closed first endpoint. -/
@[reassoc] theorem orderedOriginalBoundaryCoordinate_first (j : Fin n) :
    orderedOriginalBoundaryCoordinate f hL d V c k n j ≫ (r).left =
      pullback.snd (F).hom (i).left :=
  (originalClosedFst_isPullback f hL d V c k).lift_snd _ _ _

/-- Each independent second closed endpoint maps to the original second endpoint. -/
@[reassoc] theorem orderedOriginalBoundaryCoordinate_second (j : Fin n) :
    orderedOriginalBoundaryCoordinate f hL d V c k n j ≫ (s).left ≫ (i).left =
      orderedOriginalBoundaryInclusion f hL d V c k n ≫
        fullRelationOrderedSecond f hL d V c k n j := by
  rw [← Over.comp_left, ← originalClosedArrow_snd, Over.comp_left,
    ← Category.assoc, orderedOriginalBoundaryCoordinate_arrow, Category.assoc]
  rfl

end FLT.Mazur.HilbertChart.AffineRestriction
