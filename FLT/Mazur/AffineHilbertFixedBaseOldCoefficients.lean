/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseKernelTransport
public import FLT.Mazur.RelativeCoefficientBaseChange

/-!
# Old coefficients with their actual changed ground base

The changed projection remembers both the old coefficient morphism and the
new ground coordinate. The full original Picard relation is its kernel when
the old coefficient morphism has its full original kernel.
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
local instance fixedBaseOldCoefficientsSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

variable {T : Over (Spec (.of R))} (w : A ⟶ T)
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu
local notation "v" => RelativeCoefficientBaseChange.projection a u w
variable (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)

include hu hw in
/-- Coequalization retains the new base coordinate, even for nonmonic ground changes. -/
theorem fixedBaseOldCoefficients_condition : (p').left ≫ (v).left =
    (s').left ≫ (v).left := by
  apply (RelativeCoefficientBaseChange.projection_test_iff a u w _ _).mpr
  constructor
  · have hfst := congrArg Over.Hom.left
      (fixedBaseRelationMap_fst f a hL d V W t c k l u hu)
    have hsnd := congrArg Over.Hom.left
      (fixedBaseRelationMap_snd f a hL d V W t c k l u hu)
    change (r).left ≫ (p).left = (p').left ≫ u.left at hfst
    change (r).left ≫ (s).left = (s').left ≫ u.left at hsnd
    rw [← Category.assoc, ← hfst, Category.assoc, hw,
      ← Category.assoc, hsnd, Category.assoc]
  · exact (p').w.trans (s').w.symm

variable (H : IsPullback (fst f hL d V c k).left (snd f hL d V c k).left
  w.left w.left)

include hu hw H in
/-- The complete changed relation is the base-aware old coefficient kernel. -/
theorem fixedBaseOldCoefficients_isPullback :
    IsPullback (p').left (s').left (v).left (v).left :=
  fixedBaseModel_isPullback f a hL d V W t c k l u hu w v
    (RelativeCoefficientBaseChange.toOld a)
    (RelativeCoefficientBaseChange.projection_toOld a u w).symm hw
    (fixedBaseOldCoefficients_condition f a hL d V W t c k l u hu w hw) H

end FLT.Mazur.HilbertChart.AffineRestriction
