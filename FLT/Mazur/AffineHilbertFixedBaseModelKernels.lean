/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseRelationSchemeLift
public import FLT.Mazur.AffineHilbertModelKernelComparison

/-!
# Candidate kernels across actual changed-chart models

Commuting source and target maps induce a map of complete candidate kernels.
The original Picard relation square commutes with that map. No target square
is required to be Cartesian, flat, or surjective.
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
local instance fixedBaseModelKernelsSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

variable {T : Over (Spec (.of R))} {T' : Over (Spec (.of R'))}
  (w : A ⟶ T) (v : B ⟶ T') (b : (Over.map a).obj T' ⟶ T)
  (hv : u ≫ w = (Over.map a).map v ≫ b)
local notation "p" => fst f hL d V c k
local notation "s" => snd f hL d V c k
local notation "p'" => fst q h d W c' l
local notation "s'" => snd q h d W c' l
variable (hw : (fst f hL d V c k).left ≫ w.left = (snd f hL d V c k).left ≫ w.left)
  (hv' : (fst (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
    (fixedBaseTranslationClass f a V W t c) l).left ≫ v.left =
      (snd (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
        (fixedBaseTranslationClass f a V W t c) l).left ≫ v.left)
local notation "r" => fixedBaseRelationMap f a hL d V W t c k l u hu
local notation "m" => modelRelationKernelMap f hL d V c k w.left hw
local notation "m'" => modelRelationKernelMap q h d W c' l v.left hv'

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] in
include hv in
/-- The model triangle retains literal underlying scheme and coefficient maps. -/
theorem fixedBaseModelTriangle : u.left ≫ w.left = v.left ≫ b.left :=
  congrArg Over.Hom.left hv

/-- The constructed comparison retains both independently varying source coordinates. -/
def fixedBaseModelKernelMap : pullback v.left v.left ⟶ pullback w.left w.left :=
  pullback.lift (pullback.fst v.left v.left ≫ u.left)
    (pullback.snd v.left v.left ≫ u.left) (by
      rw [Category.assoc, Category.assoc, fixedBaseModelTriangle a u w v b hv,
        ← Category.assoc, ← Category.assoc, pullback.condition])
local notation "κ" => fixedBaseModelKernelMap a u w v b hv

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] in
@[reassoc]
theorem fixedBaseModelKernelMap_fst : κ ≫ pullback.fst w.left w.left =
    pullback.fst v.left v.left ≫ u.left := pullback.lift_fst _ _ _

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] in
@[reassoc]
theorem fixedBaseModelKernelMap_snd : κ ≫ pullback.snd w.left w.left =
    pullback.snd v.left v.left ≫ u.left := pullback.lift_snd _ _ _

/-- The original full-relation map is compatible with the newly constructed kernel map. -/
theorem fixedBaseModelRelationSquare : (r).left ≫ m = m' ≫ κ := by
  apply pullback.hom_ext
  · rw [Category.assoc, modelRelationKernelMap_fst, Category.assoc,
      fixedBaseModelKernelMap_fst, modelRelationKernelMap_fst_assoc]
    exact congrArg Over.Hom.left (fixedBaseRelationMap_fst f a hL d V W t c k l u hu)
  · rw [Category.assoc, modelRelationKernelMap_snd, Category.assoc,
      fixedBaseModelKernelMap_snd, modelRelationKernelMap_snd_assoc]
    exact congrArg Over.Hom.left (fixedBaseRelationMap_snd f a hL d V W t c k l u hu)

omit [Algebra.FiniteType ℤ R] [Algebra.FiniteType ℤ R'] in
/-- The kernel comparison lies over the actual finite-target comparison. -/
@[reassoc]
theorem fixedBaseModelKernelMap_target : κ ≫ pullback.fst w.left w.left ≫ w.left =
    (pullback.fst v.left v.left ≫ v.left) ≫ b.left := by
  rw [fixedBaseModelKernelMap_fst_assoc, Category.assoc,
    fixedBaseModelTriangle a u w v b hv]

end FLT.Mazur.HilbertChart.AffineRestriction
