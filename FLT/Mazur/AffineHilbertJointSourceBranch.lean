/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointGenericFppf
public import FLT.Mazur.AffineHilbertModelSourceBranchCoverage

/-!
# Propagated branches for actual joint Picard reselections

The branch is built from arrows of the complete reselected original relation.
Both old and new coefficient equations are preserved before any effective
region is known. Full generic point coverage and one two-sided etale seed
then construct a represented point without assuming an integral source.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
set_option backward.isDefEq.respectTransparency false
open FCurve CartierAbel SchemePicard
attribute [local irreducible] relation fst snd
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
local instance jointSourceBranchSmooth : SmoothOfRelativeDimension 1 q :=
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
local instance jointSourceBranchFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
variable {Z : Scheme} (s : Z ⟶ B.left)
local notation "b" => SchemeRelationEtaleBranchPropagation.branch p₁ q₁ s

include hu in
/-- The propagated original branch retains both coefficient morphisms literally. -/
theorem fixedBaseJoint_source_branch_coefficients :
    b ≫ u.left ≫ (finiteKernelProjection f hL d V c k).left =
      pullback.snd q₁ s ≫ s ≫ u.left ≫ (finiteKernelProjection f hL d V c k).left ∧
    b ≫ (finiteKernelProjection q h d W c' l).left =
      pullback.snd q₁ s ≫ s ≫ (finiteKernelProjection q h d W c' l).left := by
  have he := SchemeRelationEtaleBranchPropagation.branch_comp p₁ q₁ (v).left H s
  constructor
  · have hc := congrArg (fun g ↦ g ≫ r₀) he
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toOld] using hc
  · have hc := congrArg (fun g ↦ g ≫ r₁) he
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toNew] using hc

/-- Geometry of the unrestricted seed propagates along the full reselected original relation. -/
theorem fixedBaseJoint_source_branch_etale [Etale s]
    [Etale (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)] :
    Etale b ∧ Etale (b ≫ (v).left) :=
  ⟨inferInstance, SchemeRelationEtaleBranchPropagation.branch_target_etale p₁ q₁ (v).left H s⟩

variable [IrreducibleSpace (fixedBaseJointOver f a hL d V W t c k l u hu).left]
  [Etale s]
  [Etale (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)] [Nonempty Z]
include s

/-- Point coverage and the original seed construct a represented source on the new joint model. -/
theorem fixedBaseJointFppfSource_nonempty_of_source_branch
    (hg : ∀ x : (pullback (v).left (v).left : Scheme),
      (pullback.fst (v).left (v).left ≫ (v).left) x =
        genericPoint (fixedBaseJointOver f a hL d V W t c k l u hu).left →
      x ∈ Set.range (fun r : (relation q h d W c' l).left ↦
        modelRelationKernelMap q h d W c' l (v).left H r)) :
    Nonempty (modelFppfSource q h d W c' l v H).left := by
  let _ : IsNoetherian (fixedBaseJointOver f a hL d V W t c k l u hu).left :=
    fixedBaseJointTarget_isNoetherian f a hL d V W t c k l u hu
  exact modelFppfSource_nonempty_of_source_branch q h d W c' l v s H hg

end FLT.Mazur.HilbertChart.AffineRestriction
