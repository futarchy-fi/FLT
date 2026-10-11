/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothCrossInput

/-!
# Compatibility of the enlarged laws on all projective input charts

Pulling back the genuine two-domain mixed cover compares any chart law with a
mixed chart law. This proves compatibility for all four input charts on every
common scheme, including nilpotents and singular second inputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A mixed chart's actual two-domain cover detects comparison with any chart law. -/
theorem leftSmoothInputAddition_mixed_commonScheme (b c d e : Bool)
    (ha : d = false ∨ e = false) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (leftSmoothProductChartOpen W d e).toScheme)
    (h : f ≫ leftSmoothProductChartInput W b c =
      g ≫ leftSmoothProductChartInput W d e) :
    f ≫ leftSmoothInputAddition W b c = g ≫ leftSmoothInputAddition W d e := by
  let C := leftSmoothMixedCover W d e ha
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro i
  let p := (C.pullback₁ g).f i
  let q := Scheme.Cover.pullbackHom C g i
  have hi : p ≫ g = q ≫ C.f i := (Scheme.Cover.pullbackHom_map C g i).symm
  have hg : (p ≫ f) ≫ leftSmoothProductChartInput W b c =
      (q ≫ C.f i) ≫ leftSmoothProductChartInput W d e := by
    rw [Category.assoc, h, ← Category.assoc, hi]
  change p ≫ (f ≫ leftSmoothInputAddition W b c) =
    p ≫ (g ≫ leftSmoothInputAddition W d e)
  rw [← Category.assoc p g, hi, Category.assoc,
    leftSmoothInputAddition_mixed W d e ha, leftSmoothMixedLocal_glued]
  cases i
  · have hh : (p ≫ f) ≫ leftSmoothProductChartInput W b c =
        (q ≫ leftSmoothMixedProjection W d e ha false) ≫
          projectiveAdditionInclusion W (productChartCoordinate d) (productChartCoordinate e) 2 ≫
            integralCurveProductChart W d e := by
      change _ = (q ≫ leftSmoothMixedProjection W d e ha false) ≫
        mixedProductCoverInclusion W (productChartCoordinate d) (productChartCoordinate e)
          false ≫ integralCurveProductChart W d e
      simp only [Category.assoc, leftSmoothMixedProjection_inputs_assoc]
      simpa only [leftSmoothProductChartInput, Category.assoc] using hg
    simpa only [leftSmoothMixedLocal, Category.assoc] using
      leftSmoothInputAddition_commonPolynomial W b c d e (p ≫ f) _ hh
  · have hh : (p ≫ f) ≫ leftSmoothProductChartInput W b c =
        (q ≫ leftSmoothMixedAffineLift W d e ha ≫ leftSmoothAffineOverlapToInputs W d e) ≫
          (leftSmoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false := by
      simp only [Category.assoc, leftSmoothAffineOverlapToInputs_global,
        leftSmoothMixedAffineLift_inputs_assoc]
      simpa only [leftSmoothProductChartInput, Category.assoc] using hg
    simpa only [leftSmoothMixedLocal, leftSmoothAffineOverlapAddition, Category.assoc] using
      leftSmoothInputAddition_commonAffine W b c (p ≫ f) _ hh

/-- All enlarged chart laws agree whenever their original global input pairs agree. -/
theorem leftSmoothInputAddition_commonScheme (b c d e : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (g : X ⟶ (leftSmoothProductChartOpen W d e).toScheme)
    (h : f ≫ leftSmoothProductChartInput W b c =
      g ≫ leftSmoothProductChartInput W d e) :
    f ≫ leftSmoothInputAddition W b c = g ≫ leftSmoothInputAddition W d e := by
  cases d <;> cases e
  · exact leftSmoothInputAddition_mixed_commonScheme W b c false false (.inl rfl) f g h
  · exact leftSmoothInputAddition_mixed_commonScheme W b c false true (.inl rfl) f g h
  · exact leftSmoothInputAddition_mixed_commonScheme W b c true false (.inr rfl) f g h
  · cases b <;> cases c
    · exact (leftSmoothInputAddition_mixed_commonScheme W true true false false
        (.inl rfl) g f h.symm).symm
    · exact (leftSmoothInputAddition_mixed_commonScheme W true true false true
        (.inl rfl) g f h.symm).symm
    · exact (leftSmoothInputAddition_mixed_commonScheme W true true true false
        (.inr rfl) g f h.symm).symm
    · exact congrArg (fun a => a ≫ leftSmoothInputAddition W true true)
        ((cancel_mono (leftSmoothProductChartInput W true true)).mp h)

end FLT.Mazur.WeierstrassIntegralChart
