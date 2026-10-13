/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertGroundBaseEnvelopeLift

/-!
# Cartesian original envelopes after nonmonic ground-base changes

Every cone of schemes lifts through the actual full relation. In particular,
this comparison retains the independent residue-field branches in the
scheme product; it is not a statement only about pairs of topological points.
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
local instance : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
variable {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
local notation "B" => groundBaseSource f a hL d V W t k
local notation "u" => groundBaseSourceMap f a hL d V W t k
local notation "l" => groundBaseSourceChart f a hL d V W t k
local notation "h'" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h' d W c' l
local notation "s'" => snd q h' d W c' l
local notation "j" => toEnvelope f hL d V c k
local notation "j'" => toEnvelope q h' d W c' l
local notation "v" => fixedBaseRelationMap f a hL d V W t c k l u
  (groundBaseSource_square f a hL d V W t k)
local notation "m" => fixedBaseEnvelopeMap a V W t u
variable {Z : Scheme} (r : Z ⟶ (relation f hL d V c k).left)
  (e : Z ⟶ (prod (groundBaseSource f a hL d V W t k) W).left)
  (he : r ≫ (toEnvelope f hL d V c k).left = e ≫
    (fixedBaseEnvelopeMap a V W t (groundBaseSourceMap f a hL d V W t k)).left)

/-- A scheme cone acquires the new base from its independent envelope coordinate. -/
def groundBaseEnvelopeOriginal :
    (Over.map a).obj (Over.mk (e ≫ (prod B W).hom)) ⟶ relation f hL d V c k :=
  Over.homMk r (by
    change r ≫ (relation f hL d V c k).hom = (e ≫ (prod B W).hom) ≫ a
    rw [← Over.w j, ← Category.assoc, he, Category.assoc, Over.w m]
    rfl)

/-- The full relation lift for arbitrary scheme cones, with no base map assumed monic. -/
def groundBaseEnvelopeSchemeLift : Z ⟶ (relation q h' d W c' l).left :=
  (groundBaseEnvelopeConeLift f a hL d V W t c k
    (groundBaseEnvelopeOriginal f a hL d V W t c k r e he)
    (Over.homMk e rfl) (Over.OverMorphism.ext he)).left

@[reassoc]
theorem groundBaseEnvelopeSchemeLift_original :
    groundBaseEnvelopeSchemeLift f a hL d V W t c k r e he ≫ (v).left = r :=
  congrArg Over.Hom.left (groundBaseEnvelopeConeLift_original f a hL d V W t c k
    (groundBaseEnvelopeOriginal f a hL d V W t c k r e he)
    (Over.homMk e rfl) (Over.OverMorphism.ext he))

@[reassoc]
theorem groundBaseEnvelopeSchemeLift_envelope :
    groundBaseEnvelopeSchemeLift f a hL d V W t c k r e he ≫ (j').left = e :=
  congrArg Over.Hom.left (groundBaseEnvelopeConeLift_envelope f a hL d V W t c k
    (groundBaseEnvelopeOriginal f a hL d V W t c k r e he)
    (Over.homMk e rfl) (Over.OverMorphism.ext he))

/-- The original FULL relation is pulled back along the independent new envelope. -/
theorem groundBaseEnvelope_isPullback [IsOpenImmersion k.left] :
    IsPullback (v).left (j').left (j).left (m).left := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (congrArg Over.Hom.left (fixedBaseEnvelope_square f a hL d V W t c k l u
      (groundBaseSource_square f a hL d V W t k)))
    (fun z => groundBaseEnvelopeSchemeLift f a hL d V W t c k z.fst z.snd z.condition)
    (fun z => groundBaseEnvelopeSchemeLift_original
      f a hL d V W t c k z.fst z.snd z.condition)
    (fun z => groundBaseEnvelopeSchemeLift_envelope
      f a hL d V W t c k z.fst z.snd z.condition)
    (fun z w _ hw => ?_))
  apply (cancel_mono (j').left).mp
  exact hw.trans (groundBaseEnvelopeSchemeLift_envelope
    f a hL d V W t c k z.fst z.snd z.condition).symm

end FLT.Mazur.HilbertChart.AffineRestriction
