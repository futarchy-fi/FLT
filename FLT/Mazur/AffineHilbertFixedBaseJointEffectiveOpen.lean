/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointRelative
public import FLT.Mazur.AffineHilbertFixedBaseModelEffectiveOpen

/-!
# Effective opens of the actual joint model after changing Picard charts

The new joint model retains the inverse image of every old effective target
open. This follows from the original Picard relation, not a Cartesian assertion
about reselected finite targets. Further geometric coverage is not inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
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
local instance : SmoothOfRelativeDimension 1 q :=
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
local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
local notation "w" => finiteKernelProjection f hL d V c k
local notation "v" => fixedBaseJointRelativeProjection f a hL d V W t c k l u hu
local notation "b" => fixedBaseJointRelativeToOld f a hL d V W t c k l u hu
local notation "π" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "H₀" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "H₁" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu

/-- The comparison to the old model commutes as an actual relative scheme triangle. -/
theorem fixedBaseJointRelativeProjection_toOld :
    u ≫ w = (Over.map a).map v ≫ b :=
  Over.OverMorphism.ext (fixedBaseJointProjection_toOld f a hL d V W t c k l u hu).symm

/-- The effective open is computed from the complete new Picard relation. -/
def fixedBaseJointEffectiveTargetOpen :
    (fixedBaseJointTarget f a hL d V W t c k l u hu).Opens :=
  KernelPairEffectiveOpen.targetOpen p₁ q₁ π H₁

/-- Every effective old neighborhood pulls into the newly computed effective open. -/
theorem fixedBaseJointEffectiveTargetOpen_contains_old :
    (fixedBaseJointToOld f a hL d V W t c k l u hu) ⁻¹ᵁ
      KernelPairEffectiveOpen.targetOpen p₀ q₀ (w).left H₀ ≤
        fixedBaseJointEffectiveTargetOpen f a hL d V W t c k l u hu :=
  fixedBaseModelEffectiveOpen_le f a hL d V W t c k l u hu w v b
    (fixedBaseJointRelativeProjection_toOld f a hL d V W t c k l u hu) H₀ H₁

/-- The complete new relation embeds in the actual joint kernel without any effectivity premise. -/
instance fixedBaseJointRelationKernelMap_mono : Mono (pullback.lift p₁ q₁ H₁) :=
  modelRelationKernelMap_mono q h d W c' l π H₁

/-- Above the constructed open the retained full relation is an actual kernel pair. -/
theorem fixedBaseJointEffective_isPullback :
    IsPullback (KernelPairEffectiveOpen.fst p₁ q₁ π H₁)
      (KernelPairEffectiveOpen.snd p₁ q₁ π H₁)
      (KernelPairEffectiveOpen.projection p₁ q₁ π H₁)
      (KernelPairEffectiveOpen.projection p₁ q₁ π H₁) :=
  KernelPairEffectiveOpen.isPullback p₁ q₁ π H₁

end FLT.Mazur.HilbertChart.AffineRestriction
