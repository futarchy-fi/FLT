/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertJointSourceBranch
public import FLT.Mazur.SchemeSplitEtaleSourceSeed

/-!
# Split source seeds retaining both actual Picard coefficient systems

Pull the complete reselected source back by the seed's joint coefficient map.
The graph is a constructed etale seed, monic over the new target. Both old
and new coefficient equations hold on the ENTIRE pulled-back source.
No reduction of the base and no orbit coverage assumption enter this construction.
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
local instance jointSplitSeedSmooth : SmoothOfRelativeDimension 1 q :=
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
local instance jointSplitSeedFinitePresentation : LocallyOfFinitePresentation (v).left :=
  fixedBaseJointProjection_locallyOfFinitePresentation f a hL d V W t c k l u hu

local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
variable {Z : Scheme} (s : Z ⟶ B.left)
local notation "g" => SchemeSplitEtaleSourceSeed.toSource (Over.Hom.left v) s
local notation "π" => SchemeSplitEtaleSourceSeed.projection (Over.Hom.left v) s
local notation "j" => SchemeSplitEtaleSourceSeed.seed (Over.Hom.left v) s

/-- Both coefficient maps survive on the COMPLETE source after the explicit target change. -/
theorem fixedBaseJoint_split_source_coefficients :
    g ≫ u.left ≫ (finiteKernelProjection f hL d V c k).left =
      π ≫ s ≫ u.left ≫ (finiteKernelProjection f hL d V c k).left ∧
    g ≫ (finiteKernelProjection q h d W c' l).left =
      π ≫ s ≫ (finiteKernelProjection q h d W c' l).left := by
  have he := (SchemeSplitEtaleSourceSeed.isPullback (v).left s).w
  constructor
  · have hc := congrArg (fun z ↦ z ≫ r₀) he
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toOld] using hc
  · have hc := congrArg (fun z ↦ z ≫ r₁) he
    simpa only [Category.assoc, fixedBaseJointRelativeProjection,
      Over.homMk_left, fixedBaseJointProjection_toNew] using hc

/-- The full original source point is retained by the constructed graph. -/
theorem fixedBaseJoint_split_seed_point (z : Z) : g (j z) = s z :=
  SchemeSplitEtaleSourceSeed.seed_point (v).left s z

/-- The seed is now etale over the full source and literally the identity over the new target. -/
theorem fixedBaseJoint_split_seed_geometry [Etale s]
    [Etale (s ≫ (fixedBaseJointRelativeProjection f a hL d V W t c k l u hu).left)] :
    Etale g ∧ Etale j ∧ j ≫ π = 𝟙 Z :=
  ⟨inferInstance, inferInstance, SchemeSplitEtaleSourceSeed.seed_projection (v).left s⟩

end FLT.Mazur.HilbertChart.AffineRestriction
