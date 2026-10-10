/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFactorAddition

/-!
# The original polynomial and infinity formulas for global smooth addition

These comparisons apply on arbitrary common schemes and keep the original
unrestricted formula domains. They make the concrete identity and inverse
calculations available for the new global smooth law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A smooth global input pair has a smooth lift in any chosen original tensor chart. -/
def smoothProductChartLift (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (h : g ≫ integralCurveProductChart W b c = f ≫ (smoothCurveProductOpen W).ι) :
    X ⟶ (smoothProductChartOpen W b c).toScheme :=
  IsOpenImmersion.lift (smoothProductChartOpen W b c).ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨p, rfl⟩
    change (g ≫ integralCurveProductChart W b c) p ∈ smoothCurveProductOpen W
    rw [h]
    exact (f p).property)

/-- Global smooth addition retains every original polynomial output-Z presentation. -/
theorem smoothCurveAddition_originalPolynomial (b c : Bool) {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (AdditionOutputOpen W
      (productChartCoordinate b) (productChartCoordinate c) 2)))
    (h : f ≫ (smoothCurveProductOpen W).ι =
      g ≫ projectiveAdditionInclusion W (productChartCoordinate b) (productChartCoordinate c) 2 ≫
        integralCurveProductChart W b c) :
    f ≫ smoothCurveAddition W ≫ (integralSmoothOpen W).ι =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W
        (productChartCoordinate b) (productChartCoordinate c) 2).toRingHom) ≫
          integralCurveChart W 2 := by
  let a := g ≫ projectiveAdditionInclusion W
    (productChartCoordinate b) (productChartCoordinate c) 2
  have ha : a ≫ integralCurveProductChart W b c = f ≫ (smoothCurveProductOpen W).ι := by
    simpa only [a, Category.assoc] using h.symm
  let l := smoothProductChartLift W b c f a ha
  have hl : l ≫ smoothProductChartInput W b c = f ≫ (smoothCurveProductOpen W).ι := by
    rw [smoothProductChartInput, ← Category.assoc]
    exact (congrArg (fun q => q ≫ integralCurveProductChart W b c)
      (IsOpenImmersion.lift_fac _ _ _)).trans ha
  rw [← Category.assoc, smoothCurveAddition_commonScheme W b c f l hl.symm, Category.assoc]
  exact smoothInputAddition_commonPolynomial W b c b c l g (hl.trans h)

/-- Global smooth addition retains the original infinity formula on every common scheme. -/
theorem smoothCurveAddition_originalInfinity {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityAdditionOpen W)))
    (h : f ≫ (smoothCurveProductOpen W).ι =
      g ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true) :
    f ≫ smoothCurveAddition W ≫ (integralSmoothOpen W).ι =
      g ≫ infinityAdditionSpec W ≫ integralCurveChart W 1 := by
  have hs : Set.range g ⊆ infinitySmoothInputOpen W := by
    rintro _ ⟨p, rfl⟩
    apply (infinitySmoothInputOpen_preimage W).le
    change (g ≫ infinityAdditionInclusion W ≫ integralCurveProductChart W true true) p ∈
      smoothCurveProductOpen W
    rw [← h]
    exact (f p).property
  let l := IsOpenImmersion.lift (infinitySmoothInputOpen W).ι g
    (by rw [Scheme.Opens.range_ι]; exact hs)
  have hl : l ≫ (infinitySmoothInputOpen W).ι = g := IsOpenImmersion.lift_fac _ _ _
  have hi : (l ≫ smoothInfinityToInputs W) ≫ smoothProductChartInput W true true =
      f ≫ (smoothCurveProductOpen W).ι := by
    rw [Category.assoc, smoothProductChartInput, smoothInfinityToInputs_inclusion_assoc,
      smoothInfinityInput, ← Category.assoc, ← Category.assoc, hl]
    exact h.symm
  rw [← Category.assoc, smoothCurveAddition_commonScheme W true true f _ hi.symm]
  simp only [Category.assoc, smoothInputAddition_infinity_assoc, infinitySmoothChart_inclusion]
  rw [← Category.assoc, hl]
  rfl

end FLT.Mazur.WeierstrassIntegralChart
