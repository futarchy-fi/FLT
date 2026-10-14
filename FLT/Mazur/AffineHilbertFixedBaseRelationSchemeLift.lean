/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelation

/-!
# Full changed-chart relation lifts on arbitrary scheme tests

The actual coefficient-base equality is retained explicitly. Every original
relation arrow with two such new endpoints lifts uniquely to the new relation,
without assuming the coefficient-base morphism is monic or flat.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open FCurve CartierAbel SchemePicard
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
local instance fixedBaseRelationSchemeLiftSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu

/-- Arbitrary scheme tests recover the entire changed relation, with both base coordinates. -/
theorem fixedBaseRelationMap_scheme_lift {Z : Scheme} (x y : Z ⟶ B.left)
    (hb : x ≫ B.hom = y ≫ B.hom) (z : Z ⟶ (relation f hL d V c k).left)
    (hx : z ≫ (p).left = x ≫ u.left) (hy : z ≫ (s).left = y ≫ u.left) :
    ∃! v : Z ⟶ (relation q h d W c' l).left,
      v ≫ (p').left = x ∧ v ≫ (s').left = y ∧ v ≫ (r).left = z := by
  let Z' : Over (Spec (.of R')) := Over.mk (x ≫ B.hom)
  let x' : Z' ⟶ B := Over.homMk x
  let y' : Z' ⟶ B := Over.homMk y hb.symm
  let z' : (Over.map a).obj Z' ⟶ relation f hL d V c k := Over.homMk z (by
    change z ≫ (relation f hL d V c k).hom = (x ≫ B.hom) ≫ a
    rw [← (p).w, ← Category.assoc, hx, Category.assoc, u.w]
    rfl)
  obtain ⟨v, hv, huniq⟩ := fixedBaseRelationMap_lift f a hL d V W t c k l u hu x' y' z'
    (Over.OverMorphism.ext hx) (Over.OverMorphism.ext hy)
  refine ⟨v.left, ⟨congrArg Over.Hom.left hv.1, congrArg Over.Hom.left hv.2.1,
    congrArg Over.Hom.left hv.2.2⟩, ?_⟩
  intro b hb'
  let b' : Z' ⟶ relation q h d W c' l := Over.homMk b (by
    change b ≫ (relation q h d W c' l).hom = x ≫ B.hom
    rw [← (p').w, ← Category.assoc, hb'.1])
  exact congrArg Over.Hom.left (huniq b' ⟨Over.OverMorphism.ext hb'.1,
    Over.OverMorphism.ext hb'.2.1, Over.OverMorphism.ext hb'.2.2⟩)

end FLT.Mazur.HilbertChart.AffineRestriction
