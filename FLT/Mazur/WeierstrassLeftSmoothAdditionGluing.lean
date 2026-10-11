/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothInputCompatibility

/-!
# Global translation on the full left smooth projective input open

The four left left smooth input laws glue as scheme morphisms in arbitrary reduction.
The construction uses the original projective product cover and retains each
chart formula on any scheme presenting the same global inputs.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The pulled-back projective cover projects into the corresponding left smooth input chart. -/
def leftSmoothCurveProductCoverToChart (b c : Bool) :
    (leftSmoothCurveProductCover W).X (b, c) ⟶ (leftSmoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (leftSmoothProductChartOpen W b c).ι
    (leftSmoothCurveProductCoverProjection W b c) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      change (leftSmoothCurveProductCoverProjection W b c ≫
        integralCurveProductChart W b c) p ∈ leftSmoothCurveProductOpen W
      rw [leftSmoothCurveProductCoverProjection_inputs]
      exact ((leftSmoothCurveProductCover W).f (b, c) p).property)

/-- The smooth cover projection retains the original global input pair. -/
@[reassoc] theorem leftSmoothCurveProductCoverToChart_inputs (b c : Bool) :
    leftSmoothCurveProductCoverToChart W b c ≫ leftSmoothProductChartInput W b c =
      (leftSmoothCurveProductCover W).f (b, c) ≫ (leftSmoothCurveProductOpen W).ι := by
  rw [leftSmoothProductChartInput, ← Category.assoc]
  have hi : leftSmoothCurveProductCoverToChart W b c ≫ (leftSmoothProductChartOpen W b c).ι =
      leftSmoothCurveProductCoverProjection W b c := IsOpenImmersion.lift_fac _ _ _
  rw [hi, leftSmoothCurveProductCoverProjection_inputs]

/-- The full left smooth product carries addition into the original cubic. -/
def leftSmoothCurveAddition :
    (leftSmoothCurveProductOpen W).toScheme ⟶ integralCurve W :=
  (leftSmoothCurveProductCover W).glueMorphisms
    (fun p => leftSmoothCurveProductCoverToChart W p.1 p.2 ≫ leftSmoothInputAddition W p.1 p.2)
    (by
      rintro ⟨b, c⟩ ⟨d, e⟩
      have hi : (pullback.fst ((leftSmoothCurveProductCover W).f (b, c))
          ((leftSmoothCurveProductCover W).f (d, e)) ≫
          leftSmoothCurveProductCoverToChart W b c) ≫
          leftSmoothProductChartInput W b c =
        (pullback.snd ((leftSmoothCurveProductCover W).f (b, c))
          ((leftSmoothCurveProductCover W).f (d, e)) ≫
          leftSmoothCurveProductCoverToChart W d e) ≫
          leftSmoothProductChartInput W d e := by
        simp only [Category.assoc, leftSmoothCurveProductCoverToChart_inputs]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ (leftSmoothCurveProductOpen W).ι)
            (pullback.condition (f := (leftSmoothCurveProductCover W).f (b, c))
              (g := (leftSmoothCurveProductCover W).f (d, e)))).trans (Category.assoc _ _ _))
      simpa only [Category.assoc] using
        leftSmoothInputAddition_commonScheme W b c d e _ _ hi)

/-- The global law retains each of the four complete smooth chart laws. -/
@[reassoc] theorem leftSmoothCurveProductCover_addition (b c : Bool) :
    (leftSmoothCurveProductCover W).f (b, c) ≫ leftSmoothCurveAddition W =
      leftSmoothCurveProductCoverToChart W b c ≫ leftSmoothInputAddition W b c :=
  (leftSmoothCurveProductCover W).ι_glueMorphisms _ _ (b, c)

/-- The global left smooth law agrees with each chart on arbitrary common input schemes. -/
theorem leftSmoothCurveAddition_commonScheme (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (leftSmoothProductChartOpen W b c).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι = g ≫ leftSmoothProductChartInput W b c) :
    f ≫ leftSmoothCurveAddition W = g ≫ leftSmoothInputAddition W b c := by
  let C : X.OpenCover := (leftSmoothCurveProductCover W).pullback₁ f
  apply C.hom_ext
  rintro ⟨d, e⟩
  let q := (leftSmoothCurveProductCover W).pullbackHom f (d, e)
  have hq : q ≫ (leftSmoothCurveProductCover W).f (d, e) = C.f (d, e) ≫ f :=
    Scheme.Cover.pullbackHom_map _ _ _
  change C.f (d, e) ≫ (f ≫ leftSmoothCurveAddition W) =
    C.f (d, e) ≫ (g ≫ leftSmoothInputAddition W b c)
  have he : (leftSmoothCurveProductCover W).f (d, e) ≫ leftSmoothCurveAddition W =
      leftSmoothCurveProductCoverToChart W d e ≫ leftSmoothInputAddition W d e :=
    leftSmoothCurveProductCover_addition W d e
  rw [← Category.assoc, ← hq, Category.assoc, he]
  have hi : (q ≫ leftSmoothCurveProductCoverToChart W d e) ≫
      leftSmoothProductChartInput W d e = (C.f (d, e) ≫ g) ≫ leftSmoothProductChartInput W b c := by
    rw [Category.assoc, leftSmoothCurveProductCoverToChart_inputs, ← Category.assoc,
      hq, Category.assoc, h, Category.assoc]
  simpa only [Category.assoc] using leftSmoothInputAddition_commonScheme W d e b c
    (q ≫ leftSmoothCurveProductCoverToChart W d e) (C.f (d, e) ≫ g) hi

end FLT.Mazur.WeierstrassIntegralChart
