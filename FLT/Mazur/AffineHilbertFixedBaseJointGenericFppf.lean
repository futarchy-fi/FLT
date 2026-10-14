/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointFppfOpen
public import FLT.Mazur.AffineHilbertModelGenericFppf
public import FLT.Mazur.SchemeRelationJointModelGenericFppf

/-!
# Generic fppf nonemptiness after actual joint coefficient reselection

An integral reselected original source makes the joint coefficient model
integral and dominant. Its full effective Picard region has a nonempty
represented fppf target exactly when that effective region is nonempty.
Both original coefficient systems and the full original relation are retained.
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
local instance fixedBaseJointGenericFppfSmooth : SmoothOfRelativeDimension 1 q :=
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
local instance fixedBaseJointGenericFppfFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

/-- The reselected joint source projection is dominant by literal coefficient inclusion. -/
instance fixedBaseJointRelativeProjection_isDominant : IsDominant (v).left := by
  change IsDominant (SchemeRelationJointModel.projection _ _ _ _)
  infer_instance

/-- The complete reselected source projection is quasi-compact. -/
instance fixedBaseJointRelativeProjection_quasiCompact : QuasiCompact (v).left := by
  change QuasiCompact (fixedBaseJointProjection f a hL d V W t c k l u hu)
  infer_instance

variable [IsIntegral B.left]

/-- The joint model inherits integrality from the unchanged reselected source. -/
instance fixedBaseJointOver_isIntegral :
    IsIntegral (fixedBaseJointOver f a hL d V W t c k l u hu).left := by
  change IsIntegral (SchemeRelationJointModel.target _ _ _ _)
  infer_instance

/-- Generic flatness supplies a nonempty region of the joint candidate model. -/
theorem fixedBaseJointGenericFppfLocus_nonempty :
    (SchemeFppfTargetOpen.locus (v).left :
      Set (fixedBaseJointOver f a hL d V W t c k l u hu).left).Nonempty :=
  SchemeFppfTargetOpen.nonempty (v).left

/-- On the full effective relation, the fppf step preserves exactly nonemptiness. -/
theorem fixedBaseJointFppfTarget_nonempty_iff :
    Nonempty (fixedBaseJointFppfTarget f a hL d V W t c k l u hu).left ↔
      Nonempty (modelEffectiveTarget q h d W c' l v H).left :=
  modelFppfTarget_nonempty_iff q h d W c' l v H

/-- The represented original Picard region is dense inside the full effective joint target. -/
theorem fixedBaseJointEffectiveFppfLocus_dense :
    Dense (SchemeFppfTargetOpen.locus
      (modelEffectiveRelativeProjection q h d W c' l v H).left :
        Set (modelEffectiveTarget q h d W c' l v H).left) :=
  modelFppfLocus_dense q h d W c' l v H

end FLT.Mazur.HilbertChart.AffineRestriction
