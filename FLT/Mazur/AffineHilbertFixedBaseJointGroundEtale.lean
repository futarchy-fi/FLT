/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointGroundTarget
public import FLT.Mazur.AffineHilbertFixedBaseJointEtale

/-!
# Effective joint comparison with the new ground coordinate retained

The actual ground-base pullback of the old coefficient model replaces the
old target alone. Thus no monic ground change or identification of different
new ground coordinates is needed for a complete original-kernel certificate.
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
local instance jointGroundEffectiveSmooth : SmoothOfRelativeDimension 1 q :=
  MorphismProperty.pullback_snd _ _ inferInstance
local notation "h" => fixedBaseAmple f a hL
local notation "c'" => fixedBaseTranslationClass f a V W t c
local notation "P" => variableHilbertFixedBaseProjection f a hL d V W t
variable {A : Over (Spec (.of R))} {B : Over (Spec (.of R'))}
  (k : A ⟶ variableHilbertTest f d V) (l : B ⟶ variableHilbertTest (Limits.pullback.snd f a) d W)
  (u : (Over.map a).obj B ⟶ A) (hu : u ≫ k = (Over.map a).map l ≫
    variableHilbertFixedBaseProjection f a hL d V W t)

local notation "p₀" => Over.Hom.left (fst f hL d V c k)
local notation "q₀" => Over.Hom.left (snd f hL d V c k)
local notation "p₁" => Over.Hom.left (fst q h d W c' l)
local notation "q₁" => Over.Hom.left (snd q h d W c' l)
variable [Etale V.hom] [Etale W.hom] [IsAffine A.left] [IsAffine B.left]
  [IsOpenImmersion k.left] [IsOpenImmersion l.left]
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "r₀" => fixedBaseJointToGroundOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
local notation "hj" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local notation "hr" => fixedBaseJointProjection_toGroundOld f a hL d V W t c k l u hu
local notation "w" => Over.Hom.left (RelativeCoefficientBaseChange.projection a u
  (finiteKernelProjection f hL d V c k))

attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

variable [Etale (RelativeCoefficientBaseChange.projection a u
  (finiteKernelProjection f hL d V c k)).left]
  (H : IsPullback
    (fst (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
      (fixedBaseTranslationClass f a V W t c) l).left
    (snd (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
      (fixedBaseTranslationClass f a V W t c) l).left
    (RelativeCoefficientBaseChange.projection a u
      (finiteKernelProjection f hL d V c k)).left
    (RelativeCoefficientBaseChange.projection a u
      (finiteKernelProjection f hL d V c k)).left)

include H in
/-- The entire reselected source is etale over its actual joint coefficient scheme. -/
theorem fixedBaseJointProjection_etale_of_groundOld : Etale j :=
  SchemeEtaleImageDenseModel.projection_etale w H j hj r₀ hr

/-- The actual joint fppf region is compared as a scheme after the ground-base change. -/
def fixedBaseJointGroundEffectiveIso : (SchemeEtaleImageQuotient.image w).toScheme ≅
    (SchemeFppfTargetOpen.locus j).toScheme :=
  SchemeEtaleImageDenseModel.effectiveIso w H j hj r₀ hr

/-- Every new test has an actual surjective etale cover from the COMPLETE changed source. -/
theorem fixedBaseJointGround_complete_cover {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image w).toScheme) :
    Etale (SchemeEtaleImageDenseModel.completeProjection w H j hj b) ∧
    Surjective (SchemeEtaleImageDenseModel.completeProjection w H j hj b) :=
  ⟨SchemeEtaleImageDenseModel.completeProjection_etale w H j hj b r₀ hr,
    SchemeEtaleImageDenseModel.completeProjection_surjective w H j hj b r₀ hr⟩

/-- Both coefficient systems agree on the complete changed source, including nilpotents. -/
theorem fixedBaseJointGround_complete_coefficients {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image w).toScheme) :
    SchemeEtaleImageDenseModel.completeToSource w H j hj b ≫ w =
      SchemeEtaleImageDenseModel.completeProjection w H j hj b ≫ b ≫
        (SchemeEtaleImageQuotient.image w).ι ∧
    SchemeEtaleImageDenseModel.completeToSource w H j hj b ≫
      (finiteKernelProjection q h d W c' l).left =
        SchemeEtaleImageDenseModel.completeProjection w H j hj b ≫ b ≫
          SchemeEtaleImageDenseModel.comparison w H j hj ≫ r₁ := by
  refine ⟨SchemeEtaleImageDenseModel.complete_old_coefficients w H j hj b r₀ hr, ?_⟩
  have hc := SchemeEtaleImageDenseModel.complete_coefficients w H j hj b r₁
  rwa [fixedBaseJointProjection_toNew] at hc

end FLT.Mazur.HilbertChart.AffineRestriction
