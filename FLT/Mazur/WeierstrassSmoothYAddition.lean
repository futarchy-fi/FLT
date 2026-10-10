/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothYCompatibility

/-!
# Addition on the entire smooth Y/Y input chart

The affine, polynomial, and infinity formulas glue over every coefficient
ring. The resulting morphism retains each formula and is over the base.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Addition on every smooth pair of Y-chart inputs, including bad reduction fibers. -/
def smoothYAddition :
    (smoothProductChartOpen W true true).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (smoothYCover W).glueMorphisms (smoothYLocal W)
    (fun i j => smoothYLocal_commonScheme W i j _ _ pullback.condition)

/-- The glued smooth law retains all three original formulas. -/
@[reassoc] theorem smoothYLocal_glued (i : YProductCoverIndex) :
    smoothYInclusion W i ≫ smoothYAddition W = smoothYLocal W i :=
  (smoothYCover W).ι_glueMorphisms _ _ i

/-- All local formulas preserve the original coefficient morphism. -/
theorem smoothYLocal_structure (i : YProductCoverIndex) :
    smoothYLocal W i ≫ integralSmoothStructure W =
      smoothYInclusion W i ≫ (smoothProductChartOpen W true true).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  cases i
  · change smoothAffineOverlapAddition W true true ≫ _ =
      smoothAffineOverlapToChart W true true ≫ _
    rw [smoothAffineOverlapAddition_structure, smoothAffineOverlapToChart_inclusion_assoc]
    rfl
  · change polynomialSmoothChart W 1 1 2 ≫ _ = smoothPolynomialToInputs W true true 2 ≫ _
    rw [polynomialSmoothChart_structure, smoothPolynomialToInputs_inclusion_assoc]
    change (polynomialSmoothInputOpen W 1 1 2).ι ≫ _ =
      ((polynomialSmoothInputOpen W 1 1 2).ι ≫ projectiveAdditionInclusion W 1 1 2) ≫ _
    rw [Category.assoc, projectiveAdditionInclusion,
      specAlgHom_structure (additionOutputRestriction W 1 1 2)]
  · change infinitySmoothChart W ≫ _ = smoothInfinityToInputs W ≫ _
    rw [infinitySmoothChart_structure, smoothInfinityToInputs_inclusion_assoc,
      smoothInfinityInput, Category.assoc, infinityAdditionInclusion,
      specAlgHom_structure (infinityAdditionRestriction W)]

/-- The glued Y/Y law is a morphism over the original coefficient spectrum. -/
theorem smoothYAddition_structure :
    smoothYAddition W ≫ integralSmoothStructure W =
      (smoothProductChartOpen W true true).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1))) := by
  apply (smoothYCover W).hom_ext
  intro i
  change smoothYInclusion W i ≫ _ = smoothYInclusion W i ≫ _
  rw [← Category.assoc, smoothYLocal_glued, smoothYLocal_structure]

/-- Its three local formulas uniquely characterize the full smooth Y/Y addition. -/
theorem smoothYAddition_unique
    (f : (smoothProductChartOpen W true true).toScheme ⟶ (integralSmoothOpen W).toScheme)
    (hf : ∀ i, smoothYInclusion W i ≫ f = smoothYLocal W i) :
    f = smoothYAddition W := by
  apply (smoothYCover W).hom_ext
  intro i
  exact (hf i).trans (smoothYLocal_glued W i).symm

end FLT.Mazur.WeierstrassIntegralChart
