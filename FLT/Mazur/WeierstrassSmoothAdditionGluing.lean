/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothInputCompatibility

/-!
# Global addition on the full smooth projective input open

The four smooth input laws glue as scheme morphisms in arbitrary reduction.
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

/-- The pulled-back projective cover projects into the corresponding smooth input chart. -/
def smoothCurveProductCoverToChart (b c : Bool) :
    (smoothCurveProductCover W).X (b, c) ⟶ (smoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (smoothProductChartOpen W b c).ι
    (smoothCurveProductCoverProjection W b c) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨p, rfl⟩
      change (smoothCurveProductCoverProjection W b c ≫
        integralCurveProductChart W b c) p ∈ smoothCurveProductOpen W
      rw [smoothCurveProductCoverProjection_inputs]
      exact ((smoothCurveProductCover W).f (b, c) p).property)

/-- The smooth cover projection retains the original global input pair. -/
@[reassoc] theorem smoothCurveProductCoverToChart_inputs (b c : Bool) :
    smoothCurveProductCoverToChart W b c ≫ smoothProductChartInput W b c =
      (smoothCurveProductCover W).f (b, c) ≫ (smoothCurveProductOpen W).ι := by
  rw [smoothProductChartInput, ← Category.assoc]
  have hi : smoothCurveProductCoverToChart W b c ≫ (smoothProductChartOpen W b c).ι =
      smoothCurveProductCoverProjection W b c := IsOpenImmersion.lift_fac _ _ _
  rw [hi, smoothCurveProductCoverProjection_inputs]

/-- The full smooth product carries addition into the actual relative smooth curve. -/
def smoothCurveAddition :
    (smoothCurveProductOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (smoothCurveProductCover W).glueMorphisms
    (fun p => smoothCurveProductCoverToChart W p.1 p.2 ≫ smoothInputAddition W p.1 p.2)
    (by
      rintro ⟨b, c⟩ ⟨d, e⟩
      have hi : (pullback.fst ((smoothCurveProductCover W).f (b, c))
          ((smoothCurveProductCover W).f (d, e)) ≫
          smoothCurveProductCoverToChart W b c) ≫
          smoothProductChartInput W b c =
        (pullback.snd ((smoothCurveProductCover W).f (b, c))
          ((smoothCurveProductCover W).f (d, e)) ≫
          smoothCurveProductCoverToChart W d e) ≫
          smoothProductChartInput W d e := by
        simp only [Category.assoc, smoothCurveProductCoverToChart_inputs]
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun f => f ≫ (smoothCurveProductOpen W).ι)
            (pullback.condition (f := (smoothCurveProductCover W).f (b, c))
              (g := (smoothCurveProductCover W).f (d, e)))).trans (Category.assoc _ _ _))
      simpa only [Category.assoc] using
        smoothInputAddition_commonScheme W b c d e _ _ hi)

/-- The global law retains each of the four complete smooth chart laws. -/
@[reassoc] theorem smoothCurveProductCover_addition (b c : Bool) :
    (smoothCurveProductCover W).f (b, c) ≫ smoothCurveAddition W =
      smoothCurveProductCoverToChart W b c ≫ smoothInputAddition W b c :=
  (smoothCurveProductCover W).ι_glueMorphisms _ _ (b, c)

/-- The global smooth law agrees with each chart on arbitrary common input schemes. -/
theorem smoothCurveAddition_commonScheme (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ (smoothProductChartOpen W b c).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι = g ≫ smoothProductChartInput W b c) :
    f ≫ smoothCurveAddition W = g ≫ smoothInputAddition W b c := by
  let C : X.OpenCover := (smoothCurveProductCover W).pullback₁ f
  apply C.hom_ext
  rintro ⟨d, e⟩
  let q := (smoothCurveProductCover W).pullbackHom f (d, e)
  have hq : q ≫ (smoothCurveProductCover W).f (d, e) = C.f (d, e) ≫ f :=
    Scheme.Cover.pullbackHom_map _ _ _
  change C.f (d, e) ≫ (f ≫ smoothCurveAddition W) = C.f (d, e) ≫ (g ≫ smoothInputAddition W b c)
  have he : (smoothCurveProductCover W).f (d, e) ≫ smoothCurveAddition W =
      smoothCurveProductCoverToChart W d e ≫ smoothInputAddition W d e :=
    smoothCurveProductCover_addition W d e
  rw [← Category.assoc, ← hq, Category.assoc, he]
  have hi : (q ≫ smoothCurveProductCoverToChart W d e) ≫
      smoothProductChartInput W d e = (C.f (d, e) ≫ g) ≫ smoothProductChartInput W b c := by
    rw [Category.assoc, smoothCurveProductCoverToChart_inputs, ← Category.assoc,
      hq, Category.assoc, h, Category.assoc]
  simpa only [Category.assoc] using smoothInputAddition_commonScheme W d e b c
    (q ≫ smoothCurveProductCoverToChart W d e) (C.f (d, e) ≫ g) hi

end FLT.Mazur.WeierstrassIntegralChart
