/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointRelative
public import FLT.Mazur.AffineHilbertModelFppfDescent

/-!
# Actual fppf Picard regions of reselected joint models

The joint finite coefficient model has proved finite presentation. Its
constructed effective fppf region therefore has a genuine flat surjective
projection and a descended original Picard section, without global flatness
or surjectivity premises. Coverage of these regions remains a geometric task.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
open FCurve CartierAbel SchemePicard
variable {R R' : Type} [CommRing R] [CommRing R']
  [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R']
  {X : Scheme} (f : X ⟶ Spec (.of R)) (a : Spec (.of R') ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (V : Over (Spec (.of R))) (W : Over (Spec (.of R')))
  (t : (Over.map a).obj W ⟶ V) (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "q" => Limits.pullback.snd f a
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
local instance fixedBaseJointFppfOpenSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
local notation "v" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu
local notation "H" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local instance fixedBaseJointFppfOpenFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

/-- An actual effective fppf target in the reselected joint coefficient model. -/
def fixedBaseJointFppfTarget : Over (Spec (.of R')) := modelFppfTarget q h d W c' l v H

/-- Its whole source has a constructed fppf projection. -/
def fixedBaseJointFppfProjection : modelFppfSource q h d W c' l v H ⟶
    fixedBaseJointFppfTarget f a hL d V W t c k l u hu :=
  modelFppfProjection q h d W c' l v H
local notation "π" => fixedBaseJointFppfProjection f a hL d V W t c k l u hu

instance fixedBaseJointFppfProjection_flat : Flat (π).left :=
  modelFppfProjection_flat q h d W c' l v H

instance fixedBaseJointFppfProjection_surjective : Surjective (π).left :=
  modelFppfProjection_surjective q h d W c' l v H

instance fixedBaseJointFppfProjection_locallyOfFinitePresentation :
    LocallyOfFinitePresentation (π).left :=
  modelFppfProjection_locallyOfFinitePresentation q h d W c' l v H

/-- The new effective region sits in the actual joint model over the unchanged new base. -/
def fixedBaseJointFppfToModel : fixedBaseJointFppfTarget f a hL d V W t c k l u hu ⟶
    fixedBaseJointOver f a hL d V W t c k l u hu :=
  modelFppfTargetToModel q h d W c' l v H

/-- Its section belongs to the original Picard sheaf of the base-changed proper family. -/
def fixedBaseJointFppfSection : (relativeFppfSheaf q).obj.obj
    (op (fixedBaseJointFppfTarget f a hL d V W t c k l u hu)) :=
  modelFppfDescendedSection q h d W c' l v H

/-- The original source section is recovered by the actual constructed fppf cover. -/
theorem fixedBaseJointFppfSection_source :
    (relativeFppfSheaf q).obj.map (π).op
      (fixedBaseJointFppfSection f a hL d V W t c k l u hu) =
        modelFppfSection q h d W c' l v H :=
  modelFppfDescendedSection_source q h d W c' l v H

/-- All relative scheme tests are separated by the original descended Picard class. -/
theorem fixedBaseJointFppfSection_injective (Z : Over (Spec (.of R'))) :
    Function.Injective
      (fun z : Z ⟶ fixedBaseJointFppfTarget f a hL d V W t c k l u hu ↦
        (relativeFppfSheaf q).obj.map z.op
          (fixedBaseJointFppfSection f a hL d V W t c k l u hu)) :=
  modelFppfDescendedSection_injective q h d W c' l v H Z

end FLT.Mazur.HilbertChart.AffineRestriction
