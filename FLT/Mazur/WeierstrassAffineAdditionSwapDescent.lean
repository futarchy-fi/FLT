/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedMixedSchemes
public import FLT.Mazur.WeierstrassAffineAdditionGluing

/-!
# Commutativity on the entire affine input product

All sixteen pairs of original and reversed local addition laws agree as maps
to the projective cubic. Descent through the actual pulled-back addition cover
proves commutativity of the glued affine addition morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- All four affine-input laws agree as curve-valued maps on common domains. -/
theorem additionCurveChart_swap_commonScheme (i j : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ Spec (additionChartRing W i)) (g : X ⟶ Spec (additionChartRing W j))
    (hfg : f ≫ additionChartInclusion W i = g ≫ additionChartInclusion W j ≫ affineInputSwap W) :
    f ≫ additionCurveChart W i = g ≫ additionCurveChart W j := by
  have hgf : g ≫ additionChartInclusion W j =
      f ≫ additionChartInclusion W i ≫ affineInputSwap W := by
    have he := congrArg (fun t => t ≫ affineInputSwap W) hfg
    simpa only [Category.assoc, affineInputSwap_swap, Category.comp_id] using he.symm
  cases i <;> cases j
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2)
        (ordinaryAddition_swap_commonScheme W false false f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2)
        (ordinaryAddition_swap_commonScheme W false true f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_swap_curve_eq W false false f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_swap_curve_eq W false true f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2)
        (ordinaryAddition_swap_commonScheme W true false f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 2)
        (ordinaryAddition_swap_commonScheme W true true f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_swap_curve_eq W true false f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      mixedAddition_swap_curve_eq W true true f g hfg
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_swap_curve_eq W false false g f hgf).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_swap_curve_eq W true false g f hgf).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1)
        (reciprocalAddition_swap_commonScheme W false false f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1)
        (reciprocalAddition_swap_commonScheme W false true f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_swap_curve_eq W false true g f hgf).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      (mixedAddition_swap_curve_eq W true true g f hgf).symm
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1)
        (reciprocalAddition_swap_commonScheme W true false f g hfg)
  · simpa only [additionCurveChart, additionChartOutput, additionChartSpec,
      ordinaryChartAddition, reciprocalChartAddition, Category.assoc] using
      congrArg (fun t => t ≫ integralCurveChart W 1)
        (reciprocalAddition_swap_commonScheme W true true f g hfg)

/-- Every original addition domain retains its output after reversing the inputs. -/
theorem additionCurveChart_swap_glued (hΔ : IsUnit W.Δ) (i : AdditionChartIndex) :
    additionChartInclusion W i ≫ affineInputSwap W ≫ affineAdditionToCurve W hΔ =
      additionCurveChart W i := by
  let C := additionAffineOpenCover W hΔ
  let g := additionChartInclusion W i ≫ affineInputSwap W
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro j
  let p := (C.pullback₁ g).f j
  let q := Scheme.Cover.pullbackHom C g j
  have hi : q ≫ additionChartInclusion W j = p ≫ additionChartInclusion W i ≫
      affineInputSwap W := Scheme.Cover.pullbackHom_map C g j
  change p ≫ (additionChartInclusion W i ≫ affineInputSwap W ≫
    affineAdditionToCurve W hΔ) = p ≫ additionCurveChart W i
  rw [← Category.assoc (additionChartInclusion W i), ← Category.assoc p, ← hi,
    Category.assoc, additionCurveChart_glued]
  exact additionCurveChart_swap_commonScheme W j i q p hi

/-- Glued addition is commutative on the entire affine input product. -/
theorem affineAdditionToCurve_swap (hΔ : IsUnit W.Δ) :
    affineInputSwap W ≫ affineAdditionToCurve W hΔ = affineAdditionToCurve W hΔ := by
  apply Scheme.Cover.hom_ext (additionAffineOpenCover W hΔ)
  intro i
  exact (additionCurveChart_swap_glued W hΔ i).trans (additionCurveChart_glued W hΔ i).symm

end FLT.Mazur.WeierstrassIntegralChart
