/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFixedBaseJointModel
public import FLT.Mazur.SchemeRelationJointModelEtaleImage
public import FLT.Mazur.SchemeEtaleImageModelBaseChange

/-!
# Effective joint comparison after ground-base and translation changes

The original changed-family relation is retained, including both independently
varying endpoints. An effective etale old coefficient map constructs the joint
model's actual effective region and full source covers over arbitrary tests.
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
local instance jointImageSmooth : SmoothOfRelativeDimension 1 q :=
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
/-- Use the actual old coefficient base on its full invariant ring. -/
local instance jointImageOldAlgebra : Algebra R
    (SchemeEffectiveEpiSections.compatibleFunctions p₀ q₀) :=
  (invariantCoefficientBase f hL d V c k).toAlgebra
/-- Use the actual changed coefficient base on its full invariant ring. -/
local instance jointImageNewAlgebra : Algebra R'
    (SchemeEffectiveEpiSections.compatibleFunctions p₁ q₁) :=
  (invariantCoefficientBase q h d W c' l).toAlgebra
local notation "C₀" => finiteKernelCoefficientAlgebra f hL d V c k
local notation "C₁" => finiteKernelCoefficientAlgebra q h d W c' l

local notation "α" => fixedBaseOldFiniteCoefficients f a hL d V W t c k l u hu
local notation "β" => AlgHom.toRingHom (Subalgebra.val C₁)
local notation "j" => fixedBaseJointProjection f a hL d V W t c k l u hu
local notation "r₀" => fixedBaseJointToOld f a hL d V W t c k l u hu
local notation "r₁" => fixedBaseJointToNew f a hL d V W t c k l u hu
local notation "hj" => fixedBaseJointProjection_condition f a hL d V W t c k l u hu
local notation "hr" => fixedBaseJointProjection_toOld f a hL d V W t c k l u hu
local notation "w" => u.left ≫ Over.Hom.left (finiteKernelProjection f hL d V c k)

instance fixedBaseJointProjection_schematicallyDominant :
    IsSchemeTheoreticallyDominant (fixedBaseJointProjection f a hL d V W t c k l u hu) :=
  SchemeRelationJointModel.projection_schematicallyDominant p₁ q₁ α β

instance fixedBaseJointProjection_quasiCompact :
    QuasiCompact (fixedBaseJointProjection f a hL d V W t c k l u hu) := by infer_instance

attribute [local irreducible] relation fst snd finiteKernelProjection finiteKernelModel
  fixedBaseJointProjection fixedBaseJointTarget fixedBaseJointToOld fixedBaseJointToNew

variable [Etale (u.left ≫ (finiteKernelProjection f hL d V c k).left)]
  (H : IsPullback
    (fst (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
      (fixedBaseTranslationClass f a V W t c) l).left
    (snd (Limits.pullback.snd f a) (fixedBaseAmple f a hL) d W
      (fixedBaseTranslationClass f a V W t c) l).left
    (u.left ≫ (finiteKernelProjection f hL d V c k).left)
    (u.left ≫ (finiteKernelProjection f hL d V c k).left))

include H in
/-- The entire reselected source is etale over its actual joint coefficient scheme. -/
theorem fixedBaseJointProjection_etale_of_old : Etale j :=
  SchemeEtaleImageDenseModel.projection_etale w H j hj r₀ hr

/-- The actual joint fppf region is compared as a scheme after the ground-base change. -/
def fixedBaseJointEtaleEffectiveIso : (SchemeEtaleImageQuotient.image w).toScheme ≅
    (SchemeFppfTargetOpen.locus j).toScheme :=
  SchemeEtaleImageDenseModel.effectiveIso w H j hj r₀ hr

/-- Every new test has an actual surjective etale cover from the COMPLETE changed source. -/
theorem fixedBaseJointEtale_complete_cover {Y : Scheme}
    (b : Y ⟶ (SchemeEtaleImageQuotient.image w).toScheme) :
    Etale (SchemeEtaleImageDenseModel.completeProjection w H j hj b) ∧
    Surjective (SchemeEtaleImageDenseModel.completeProjection w H j hj b) :=
  ⟨SchemeEtaleImageDenseModel.completeProjection_etale w H j hj b r₀ hr,
    SchemeEtaleImageDenseModel.completeProjection_surjective w H j hj b r₀ hr⟩

/-- Both coefficient systems agree on the complete changed source, including nilpotents. -/
theorem fixedBaseJointEtale_complete_coefficients {Y : Scheme}
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
