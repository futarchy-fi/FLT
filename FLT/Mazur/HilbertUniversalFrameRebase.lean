/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertRebasedCompleteFrame
public import FLT.Mazur.RelativeUniversalDistinctLift

/-!
# Rebasing ordered frames on arbitrary scheme tests

The entire original frame can be rebased along any original relation arrow,
on an arbitrary scheme test. Universal distinctness excludes every collision
scheme and gives an actual map to the distinct-tuple scheme. The construction
retains every independent second endpoint and needs no completeness hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples EquivalenceRelationFiber
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A T : Scheme} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q) (I : Type) [Fintype I]
  (a : T ⟶ D)

local instance overFirst_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

variable (t : Over.mk (a ≫ p) ⟶ distinctScheme (Over.mk p) I)

/-- Each original coordinate is a section over the first endpoint. -/
def originalSection (i : I) : EquivalenceRelationFiber.Sections (p := p) (a ≫ p) :=
  ⟨(t ≫ distinctCoordinate (Over.mk p) I i).left,
    (t ≫ distinctCoordinate (Over.mk p) I i).w⟩

/-- Transport the original coordinate along the original arrow on the whole test. -/
def rebaseCoordinate (i : I) : Over.mk (a ≫ q) ⟶ Over.mk p :=
  Over.homMk (sectionRebase e a (originalSection I a t i)).val
    (sectionRebase e a (originalSection I a t i)).property

/-- The original independent second endpoint is unchanged on the entire scheme test. -/
@[reassoc] theorem rebaseCoordinate_second (i : I) :
    (rebaseCoordinate e I a t i).left ≫ q =
      (t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q :=
  sectionRebase_second e a (originalSection I a t i)

/-- Rebasing retains distinct coordinates after every nonempty scheme test change. -/
theorem rebaseCoordinate_universally_injective (U : Over A) (z : U ⟶ Over.mk (a ≫ q))
    (hU : Nonempty U.left) :
    Function.Injective (fun i ↦ z ≫ rebaseCoordinate e I a t i) := by
  let _ : Nonempty U.left := hU
  intro i j hij
  apply distinctCoordinate_left_injective (Over.mk p) I (z.left ≫ t.left)
  dsimp only
  rw [Category.assoc, Category.assoc]
  change z.left ≫ (originalSection I a t i).val = z.left ≫ (originalSection I a t j).val
  apply e.right_cancellation
  · simp only [Category.assoc, (originalSection I a t i).property,
      (originalSection I a t j).property]
  · have h := congrArg (fun r ↦ r.left ≫ q) hij
    change (z.left ≫ (rebaseCoordinate e I a t i).left) ≫ q =
      (z.left ≫ (rebaseCoordinate e I a t j).left) ≫ q at h
    simpa only [Category.assoc, rebaseCoordinate_second, originalSection] using h

/-- An actual rebased distinct-frame morphism on any scheme test. -/
def rebaseFrame : Over.mk (a ≫ q) ⟶ distinctScheme (Over.mk p) I :=
  universalDistinctLift (Over.mk p) I (rebaseCoordinate e I a t)
    (rebaseCoordinate_universally_injective e I a t)

/-- The rebased frame retains every constructed original coordinate. -/
@[reassoc] theorem rebaseFrame_coordinate (i : I) :
    rebaseFrame e I a t ≫ distinctCoordinate (Over.mk p) I i =
      rebaseCoordinate e I a t i :=
  universalDistinctLift_coordinate (Over.mk p) I (rebaseCoordinate e I a t)
    (rebaseCoordinate_universally_injective e I a t) i

/-- Rebasing retains each independent original second endpoint as a scheme morphism. -/
@[reassoc] theorem rebaseFrame_second (i : I) :
    (rebaseFrame e I a t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q =
      (t ≫ distinctCoordinate (Over.mk p) I i).left ≫ q := by
  rw [rebaseFrame_coordinate, rebaseCoordinate_second]

include e in
/-- Frames over the same first endpoint are determined by all their second endpoints. -/
theorem frame_ext_second {b : T ⟶ A}
    {u v : Over.mk b ⟶ distinctScheme (Over.mk p) I}
    (h : ∀ i, (u ≫ distinctCoordinate (Over.mk p) I i).left ≫ q =
      (v ≫ distinctCoordinate (Over.mk p) I i).left ≫ q) : u = v := by
  apply distinct_hom_ext (Over.mk p) I
  intro i
  apply Over.OverMorphism.ext
  apply e.right_cancellation
  · exact (u ≫ distinctCoordinate (Over.mk p) I i).w.trans
      (v ≫ distinctCoordinate (Over.mk p) I i).w.symm
  · exact h i

end FLT.Mazur.EquivalenceRelationOrderedFrames

namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  {T : Scheme} (a : T ⟶ (relation f hL d V c k).left) (n : ℕ)
  (t : Over.mk (a ≫ (fst f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
local notation "E" => fullRelationOverFirst f hL d V c k
local notation "q" => snd f hL d V c k

/-- The original Hilbert frame rebased along an arbitrary original arrow on any scheme test. -/
def universalFullRelationFrameRebase :
    Over.mk (a ≫ (q).left) ⟶ fullRelationOrderedPoints f hL d V c k n :=
  EquivalenceRelationOrderedFrames.rebaseFrame
    (fullRelationSchemeEquivalence f hL d V c k) (Fin n) a t

omit [Etale V.hom] in
/-- Every independent original second endpoint is preserved by the arbitrary-test construction. -/
@[reassoc] theorem universalFullRelationFrameRebase_second (i : Fin n) :
    (universalFullRelationFrameRebase f hL d V c k a n t ≫
      distinctCoordinate E (Fin n) i).left ≫ (q).left =
        (t ≫ distinctCoordinate E (Fin n) i).left ≫ (q).left :=
  EquivalenceRelationOrderedFrames.rebaseFrame_second
    (fullRelationSchemeEquivalence f hL d V c k) (Fin n) a t i

/-- The arbitrary-test construction agrees with the complete geometric transport. -/
theorem universalFullRelationFrameRebase_eq_geometric {K : Type} [Field K]
    (g : Spec (.of K) ⟶ (relation f hL d V c k).left)
    (v : Over.mk (g ≫ (fst f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
    (hv : Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) v i default)) :
    universalFullRelationFrameRebase f hL d V c k g n v =
      rebasedCompleteFrame f hL d V c k g n v hv := by
  let _ : Subsingleton (Over.mk (g ≫ (q).left)).left :=
    inferInstanceAs (Subsingleton (Spec (.of K)))
  apply EquivalenceRelationOrderedFrames.frame_ext_second
    (fullRelationSchemeEquivalence f hL d V c k) (Fin n)
  intro i
  have hc : rebasedCompleteFrame f hL d V c k g n v hv ≫
      distinctCoordinate E (Fin n) i = rebasedFrameCoordinate f hL d V c k g n v i :=
    distinctLift_coordinate E (Fin n) (rebasedFrameCoordinate f hL d V c k g n v)
      (rebasedFrameCoordinate_injective f hL d V c k g n v hv) i
  exact (universalFullRelationFrameRebase_second f hL d V c k g n v i).trans
    ((congrArg (fun w : Over.mk (g ≫ (q).left) ⟶ E ↦ w.left ≫ (q).left) hc).trans
      (rebasedFrameCoordinate_second f hL d V c k g n v i)).symm

/-- The scheme-level rebase preserves completeness on every original geometric test. -/
theorem universalFullRelationFrameRebase_complete {K : Type} [Field K]
    (g : Spec (.of K) ⟶ (relation f hL d V c k).left)
    (v : Over.mk (g ≫ (fst f hL d V c k).left) ⟶ fullRelationOrderedPoints f hL d V c k n)
    (hv : Function.Bijective (fun i ↦ geometricCoordinate E (Fin n) v i default)) :
    Function.Bijective (fun i ↦ geometricCoordinate E (Fin n)
      (universalFullRelationFrameRebase f hL d V c k g n v) i default) := by
  rw [universalFullRelationFrameRebase_eq_geometric f hL d V c k n g v hv]
  exact rebasedCompleteFrame_complete f hL d V c k g n v hv

end FLT.Mazur.HilbertChart.AffineRestriction
