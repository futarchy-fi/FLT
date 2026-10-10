/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFormulaComparison

/-!
# Ordinary replacements for affine-valued smooth sums

An affine presentation of the actual smooth sum forces the normalized output
coordinate to be a unit. This gives an ordinary chart with the same inputs,
including at bad reduction and over nonreduced coefficient rings.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- An affine presentation of a smooth sum forces its chart output coordinate to be a unit. -/
theorem smoothAdditionOutput_isUnit_of_affine {X : Scheme.{u}}
    (p : X ⟶ smoothFactorProduct W) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ chartScheme W 2)
    (hf : f ≫ additionGlobalDomain W i = p ≫ smoothFactorsInclusion W)
    (hg : p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      g ≫ integralCurveChart W 2) :
    IsUnit (specSectionHom f
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))) := by
  have h := (smoothFactorAddition_chart W p i f hf).symm.trans hg
  have hu := chartCoordinate_isUnit_of_global_eq W (additionChartOutput i) 2
    (f ≫ Spec.map (CommRingCat.ofHom (additionChartAlgOutput W i).toRingHom)) g
    ((Category.assoc _ _ _).trans h)
  rw [specSectionHom_comp] at hu
  exact hu

/-- An affine-valued chart on smooth inputs has an ordinary replacement preserving the pair. -/
theorem exists_ordinary_of_smoothAddition_affine {X : Scheme.{u}}
    (p : X ⟶ smoothFactorProduct W) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ chartScheme W 2)
    (hf : f ≫ additionGlobalDomain W i = p ≫ smoothFactorsInclusion W)
    (hg : p ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι =
      g ≫ integralCurveChart W 2) :
    ∃ f' : X ⟶ Spec (additionChartRing W (ordinaryIndex (additionOrdinaryChoice i))),
      f' ≫ ordinaryGlobalDomain W (additionOrdinaryChoice i) = f ≫ additionGlobalDomain W i := by
  let hz := smoothAdditionOutput_isUnit_of_affine W p i f g hf hg
  exact ⟨additionAffineOutputScheme W i f hz, additionAffineOutputScheme_inputs W i f hz⟩

end FLT.Mazur.WeierstrassIntegralChart
