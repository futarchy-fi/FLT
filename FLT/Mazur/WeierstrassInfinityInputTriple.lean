/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityProductFlat
public import FLT.Mazur.WeierstrassIntegralTripleProduct

/-!
# The actual triple infinity-input chart

This fiber product is an open subscheme of the original triple product.
Its three projections to the infinity chart are flat over every base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity product chart has its original coefficient map. -/
theorem infinityProductChart_structure :
    integralCurveProductChart W true true ≫ integralCurveProductStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  rw [integralCurveProductStructure, ← Category.assoc, integralCurveProductChart_fst,
    Category.assoc, integralCurveChart_structure]
  exact specAlgHom_base R (chartProductLeft W 1 1)

/-- Three genuine infinity chart inputs, before imposing any addition domains. -/
abbrev InfinityInputTriple :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))))
    (chartStructure W 1)

/-- Projection to the first two input charts. -/
abbrev infinityInputTriplePair :
    InfinityInputTriple W ⟶ Spec (.of (ChartProduct W 1 1)) := pullback.fst _ _

/-- Projection to the last input chart. -/
abbrev infinityInputTripleThird :
    InfinityInputTriple W ⟶ Spec (.of (Coordinate W 1)) := pullback.snd _ _

/-- Projection to the first input chart. -/
def infinityInputTripleFirst : InfinityInputTriple W ⟶ Spec (.of (Coordinate W 1)) :=
  infinityInputTriplePair W ≫
    Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom)

/-- Projection to the middle input chart. -/
def infinityInputTripleSecond : InfinityInputTriple W ⟶ Spec (.of (Coordinate W 1)) :=
  infinityInputTriplePair W ≫
    Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom)

/-- The input triple embeds into the original curve triple. -/
def infinityInputTripleInclusion : InfinityInputTriple W ⟶ integralCurveTriple W :=
  pullback.map _ _ _ _ (integralCurveProductChart W true true) (integralCurveChart W 1)
    (𝟙 _) ((Category.comp_id _).trans (infinityProductChart_structure W).symm)
    ((Category.comp_id _).trans (integralCurveChart_structure W 1).symm)

/-- This is an actual open chart, with no affine-source assumption on later restrictions. -/
instance infinityInputTripleInclusion_isOpenImmersion :
    IsOpenImmersion (infinityInputTripleInclusion W) := by
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (inferInstance : IsOpenImmersion (integralCurveProductChart W true true))
    (inferInstance : IsOpenImmersion (integralCurveChart W 1))
    (infinityProductChart_structure W).symm (integralCurveChart_structure W 1).symm

/-- The first two original inputs are the tensor pair projection. -/
@[reassoc (attr := simp)] theorem infinityInputTripleInclusion_pair :
    infinityInputTripleInclusion W ≫ integralCurveTriplePair W =
      infinityInputTriplePair W ≫ integralCurveProductChart W true true := by
  simp [infinityInputTripleInclusion]

/-- The third original input is the last chart projection. -/
@[reassoc (attr := simp)] theorem infinityInputTripleInclusion_third :
    infinityInputTripleInclusion W ≫ integralCurveTripleThird W =
      infinityInputTripleThird W ≫ integralCurveChart W 1 := by
  simp [infinityInputTripleInclusion]

/-- Flatness of the first chart projection. -/
instance infinityInputTripleFirst_flat : Flat (infinityInputTripleFirst W) := by
  unfold infinityInputTripleFirst
  infer_instance

/-- Flatness of the middle chart projection. -/
instance infinityInputTripleSecond_flat : Flat (infinityInputTripleSecond W) := by
  unfold infinityInputTripleSecond
  infer_instance

/-- Flatness of the third chart projection. -/
instance infinityInputTripleThird_flat : Flat (infinityInputTripleThird W) := by
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
