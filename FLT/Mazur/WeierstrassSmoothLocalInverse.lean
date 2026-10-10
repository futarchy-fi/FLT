/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothOriginalAffine
public import FLT.Mazur.WeierstrassSmoothNegationGraphs
public import FLT.Mazur.WeierstrassInfinityInverseScheme

/-!
# Smooth inverse laws on affine and infinity presentations

The original regular inverse formulas remain valid under full smooth addition,
on arbitrary common schemes. Both calculations are over the original base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The inverse identity holds for every smooth affine presentation. -/
theorem smoothCurveAddition_rightNegation_affine {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ chartScheme W 2)
    (h : f ≫ (integralSmoothOpen W).ι = g ≫ integralCurveChart W 2) :
    f ≫ smoothProductRightNegation W ≫ smoothCurveAddition W =
      f ≫ integralSmoothStructure W ≫ integralSmoothZero W := by
  let a := g ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)
  have hi : (f ≫ smoothProductRightNegation W) ≫ (smoothCurveProductOpen W).ι =
      a ≫ integralCurveProductChart W false false := by
    rw [Category.assoc, smoothProductRightNegation_inclusion, ← Category.assoc, h,
      Category.assoc, integralCurveChart_rightNegation_affine]
    rfl
  have hs : Set.range a ⊆ affineAdditionDomain W := by
    intro p hp
    apply smoothAffineInputOpen_le_domain W
    apply (smoothProductChartOpen_affine W).le
    obtain ⟨x, rfl⟩ := hp
    change (a ≫ integralCurveProductChart W false false) x ∈ smoothCurveProductOpen W
    rw [← hi]
    exact ((f ≫ smoothProductRightNegation W) x).property
  let l := IsOpenImmersion.lift (affineAdditionDomain W).ι a
    (by rw [Scheme.Opens.range_ι]; exact hs)
  have hl : l ≫ (affineAdditionDomain W).ι = a := IsOpenImmersion.lift_fac _ _ _
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalPartial W (f ≫ smoothProductRightNegation W) l
    (by rw [← Category.assoc, hl]; exact hi)
  rw [affinePartialAddition_negation_commonScheme W l g hl] at he
  simp only [Category.assoc, integralSmoothZero_inclusion] at *
  rw [he, ← Category.assoc f, h, Category.assoc,
    ← Category.assoc (integralCurveChart W 2), integralCurveChart_structure]

/-- The inverse identity holds on the full constructed infinity inverse neighborhood. -/
theorem smoothCurveAddition_rightNegation_neighborhood {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityInverseOpen W)))
    (h : f ≫ (integralSmoothOpen W).ι =
      g ≫ infinityInverseInclusion W ≫ integralCurveChart W 1) :
    f ≫ smoothProductRightNegation W ≫ smoothCurveAddition W =
      f ≫ integralSmoothStructure W ≫ integralSmoothZero W := by
  have hs : infinityInverseInclusion W ≫ integralCurveChart W 1 ≫
      integralCurveRightNegation W =
      Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [infinityInverseInclusion_factor, Category.assoc, ← infinityNegationInput_spec,
      ← Category.assoc, ← infinityInverseSpec_inputs, Category.assoc]
  have hi : (f ≫ smoothProductRightNegation W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom)) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [Category.assoc, smoothProductRightNegation_inclusion, ← Category.assoc, h]
    simp only [Category.assoc]
    rw [hs]
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalInfinity W (f ≫ smoothProductRightNegation W)
    (g ≫ Spec.map (CommRingCat.ofHom (infinityInverseMap W).toRingHom)) hi
  simp only [Category.assoc] at he
  rw [infinityInverseSpec_addition] at he
  simp only [Category.assoc, integralSmoothZero_inclusion]
  rw [he, ← Category.assoc f, h]
  simp only [Category.assoc]
  rw [← Category.assoc (integralCurveChart W 1), integralCurveChart_structure, chartStructure,
    ← Category.assoc (infinityInverseInclusion W),
    show infinityInverseInclusion W ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (Coordinate W 1))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityInverseOpen W))) from
        specAlgHom_structure (infinityInverseRestriction W)]

end FLT.Mazur.WeierstrassIntegralChart
