/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertSymmetricNeighborhoods
public import FLT.Mazur.RelativeDistinctFreeAction
public import FLT.Mazur.RelativeDistinctTupleLift

/-!
# Ordered-point geometry of the full original Hilbert relation

Apply the ordered distinct-point construction to the entire first-endpoint
morphism. Every coordinate is an original relation arrow, retaining its
independent second endpoint and the unchanged coefficient map. The constructed
scheme is etale over the original source and has a free permutation action.
No finite branch is chosen and no coverage by complete frames is asserted.
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

/-- The entire relation over its original first endpoint, with no branch restriction. -/
def fullRelationOverFirst : Over A.left := Over.mk (p).left

instance fullRelationOverFirst_etale : Etale (fullRelationOverFirst f hL d V c k).hom :=
  inferInstanceAs (Etale (p).left)

instance fullRelationOverFirst_separated :
    IsSeparated (fullRelationOverFirst f hL d V c k).hom :=
  inferInstanceAs (IsSeparated (p).left)

open RelativeOrderedTuples
local notation "E" => fullRelationOverFirst f hL d V c k
variable (n : ℕ)

/-- Ordered distinct original arrows with their common original first endpoint. -/
def fullRelationOrderedPoints : Over A.left := distinctScheme E (Fin n)

/-- Every original second endpoint remains present as an independent coordinate. -/
def fullRelationOrderedSecond (i : Fin n) :
    (fullRelationOrderedPoints f hL d V c k n).left ⟶ A.left :=
  (distinctCoordinate E (Fin n) i).left ≫ (q).left

omit [Etale V.hom] in
/-- Every coordinate still has the original first endpoint. -/
@[reassoc] theorem fullRelationOrdered_first (i : Fin n) :
    (distinctCoordinate E (Fin n) i).left ≫ (p).left =
      (fullRelationOrderedPoints f hL d V c k n).hom :=
  (distinctCoordinate E (Fin n) i).w

omit [Etale V.hom] in
/-- The second endpoint keeps the unchanged original coefficient morphism. -/
@[reassoc] theorem fullRelationOrderedSecond_base (i : Fin n) :
    fullRelationOrderedSecond f hL d V c k n i ≫ A.hom =
      (fullRelationOrderedPoints f hL d V c k n).hom ≫ A.hom := by
  rw [fullRelationOrderedSecond, Category.assoc, Over.w q,
    ← Over.w p, ← Category.assoc, fullRelationOrdered_first]

/-- The actual ordered-point scheme is etale over the original Hilbert source. -/
instance fullRelationOrderedPoints_etale :
    Etale (fullRelationOrderedPoints f hL d V c k n).hom :=
  inferInstanceAs (Etale (distinctScheme E (Fin n)).hom)

/-- The finite permutation action on the constructed whole-relation ordered-point scheme. -/
def fullRelationOrderedAction :
    Equiv.Perm (Fin n) →* Aut (fullRelationOrderedPoints f hL d V c k n).left :=
  distinctAction E (Fin n)

omit [Etale V.hom] in
/-- The constructed action fixes the original first endpoint. -/
@[reassoc] theorem fullRelationOrderedAction_first (e : Equiv.Perm (Fin n)) :
    (fullRelationOrderedAction f hL d V c k n e).hom ≫
      (fullRelationOrderedPoints f hL d V c k n).hom =
        (fullRelationOrderedPoints f hL d V c k n).hom := distinctAction_base E (Fin n) e

omit [Etale V.hom] in
/-- The independent second endpoints are permuted, rather than identified. -/
@[reassoc] theorem fullRelationOrderedAction_second (e : Equiv.Perm (Fin n)) (i : Fin n) :
    (fullRelationOrderedAction f hL d V c k n e).hom ≫
      fullRelationOrderedSecond f hL d V c k n i =
        fullRelationOrderedSecond f hL d V c k n (e.symm i) := by
  change (distinctAction E (Fin n) e).hom ≫
    (distinctCoordinate E (Fin n) i).left ≫ (q).left = _
  rw [← Category.assoc, distinctAction_coordinate]
  rfl

omit [Etale V.hom] in
/-- Geometric freeness holds on the actual full-relation ordered-point scheme. -/
theorem fullRelationOrderedAction_free (K : Type) [Field K]
    (a : Spec (.of K) ⟶ (fullRelationOrderedPoints f hL d V c k n).left)
    (e : Equiv.Perm (Fin n))
    (he : a ≫ (fullRelationOrderedAction f hL d V c k n e).hom = a) : e = 1 :=
  distinctAction_field_free E (Fin n) K a e he

end FLT.Mazur.HilbertChart.AffineRestriction
