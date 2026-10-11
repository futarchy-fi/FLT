/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothAdditionGluing

/-!
# Original formulas for global translation on the whole cubic

The global law retains the enlarged affine, polynomial output-Z and infinity
formulas on all common input schemes. No reduction hypothesis is imposed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A left smooth global pair lifts to the left smooth restriction of any input chart. -/
def leftSmoothProductChartLift (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (h : g ≫ integralCurveProductChart W b c = f ≫ (leftSmoothCurveProductOpen W).ι) :
    X ⟶ (leftSmoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (leftSmoothProductChartOpen W b c).ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    change (g ≫ integralCurveProductChart W b c) p ∈ leftSmoothCurveProductOpen W
    rw [h]
    exact (f p).property)

/-- The chart lift retains the prescribed coordinates. -/
@[reassoc] theorem leftSmoothProductChartLift_inclusion (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (h : g ≫ integralCurveProductChart W b c = f ≫ (leftSmoothCurveProductOpen W).ι) :
    leftSmoothProductChartLift W b c f g h ≫ (leftSmoothProductChartOpen W b c).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- Global translation retains its actual enlarged affine law. -/
theorem leftSmoothCurveAddition_originalAffine {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (leftSmoothAffineInputOpen W).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ (leftSmoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ leftSmoothCurveAddition W = g ≫ leftSmoothAffineAddition W := by
  have hg : (g ≫ (leftSmoothAffineInputOpen W).ι) ≫ integralCurveProductChart W false false =
      f ≫ (leftSmoothCurveProductOpen W).ι := by simpa only [Category.assoc] using h.symm
  let l := leftSmoothProductChartLift W false false f _ hg
  have hl : l ≫ leftSmoothProductChartInput W false false =
      f ≫ (leftSmoothCurveProductOpen W).ι := by
    rw [leftSmoothProductChartInput, leftSmoothProductChartLift_inclusion_assoc]
    exact hg
  rw [leftSmoothCurveAddition_commonScheme W false false f l hl.symm]
  exact leftSmoothInputAddition_commonAffine W false false l g (hl.trans h)

/-- Global translation retains the original polynomial output-Z law. -/
theorem leftSmoothCurveAddition_originalPolynomial (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2)))
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c) :
    f ≫ leftSmoothCurveAddition W =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let a := g ≫ projectiveAdditionInclusion W
    (productChartCoordinate b) (productChartCoordinate c) 2
  have ha : a ≫ integralCurveProductChart W b c = f ≫ (leftSmoothCurveProductOpen W).ι := by
    simpa only [a, Category.assoc] using h.symm
  let l := leftSmoothProductChartLift W b c f a ha
  have hl : l ≫ leftSmoothProductChartInput W b c = f ≫ (leftSmoothCurveProductOpen W).ι := by
    rw [leftSmoothProductChartInput, leftSmoothProductChartLift_inclusion_assoc]
    exact ha
  rw [leftSmoothCurveAddition_commonScheme W b c f l hl.symm]
  exact leftSmoothInputAddition_commonPolynomial W b c b c l g (hl.trans h)

/-- Global translation retains the original regular infinity law. -/
theorem leftSmoothCurveAddition_originalInfinity {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true) :
    f ≫ leftSmoothCurveAddition W = g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  have ha : (g ≫ infinityAdditionInclusion W) ≫ integralCurveProductChart W true true =
      f ≫ (leftSmoothCurveProductOpen W).ι := by simpa only [Category.assoc] using h.symm
  let l := leftSmoothProductChartLift W true true f _ ha
  have hl : l ≫ leftSmoothProductChartInput W true true =
      f ≫ (leftSmoothCurveProductOpen W).ι := by
    rw [leftSmoothProductChartInput, leftSmoothProductChartLift_inclusion_assoc]
    exact ha
  rw [leftSmoothCurveAddition_commonScheme W true true f l hl.symm]
  exact leftSmoothYAddition_infinity W l g
    (leftSmoothProductChartLift_inclusion W true true f _ ha)

end FLT.Mazur.WeierstrassIntegralChart
