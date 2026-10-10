/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionOriginalFormulas
public import FLT.Mazur.WeierstrassSmoothZeroGraphs
public import FLT.Mazur.WeierstrassInfinityIdentityNeighborhood
public import FLT.Mazur.WeierstrassGlobalAdditionZeroRestrictions

/-!
# The identity laws on the smooth infinity neighborhoods

The concrete infinity neighborhoods retain both identity laws under the
full smooth addition, on arbitrary common schemes and over every base ring.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Zero on the left fixes every smooth presentation in its infinity neighborhood. -/
theorem smoothCurveAddition_leftZero_neighborhood {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityIdentityOpen W true)))
    (h : f ≫ (integralSmoothOpen W).ι =
      g ≫ infinityIdentityInclusion W true ≫ integralCurveChart W 1) :
    f ≫ smoothProductLeftZero W ≫ smoothCurveAddition W = f := by
  have hc := integralCurveChart_leftZero W true
  change integralCurveChart W 1 ≫ integralCurveLeftZero W = _ at hc
  have hi : (f ≫ smoothProductLeftZero W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W true).toRingHom)) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [Category.assoc, smoothProductLeftZero_inclusion, ← Category.assoc, h]
    simp only [Category.assoc]
    rw [hc]
    change g ≫ infinityIdentityInclusion W true ≫
      Spec.map (CommRingCat.ofHom (infinityIdentityInput W true).toRingHom) ≫ _ = _
    rw [← Category.assoc (infinityIdentityInclusion W true),
      ← infinityIdentitySpec_inputs]
    simp only [Category.assoc]
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalInfinity W
    (f ≫ smoothProductLeftZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W true).toRingHom)) hi
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (infinityIdentityMap W true).toRingHom)), infinityIdentitySpec_addition] at he
  simpa only [Category.assoc, h] using he

/-- Zero on the right fixes every smooth presentation in its infinity neighborhood. -/
theorem smoothCurveAddition_rightZero_neighborhood {X : Scheme.{u}}
    (f : X ⟶ (integralSmoothOpen W).toScheme)
    (g : X ⟶ Spec (.of (InfinityIdentityOpen W false)))
    (h : f ≫ (integralSmoothOpen W).ι =
      g ≫ infinityIdentityInclusion W false ≫ integralCurveChart W 1) :
    f ≫ smoothProductRightZero W ≫ smoothCurveAddition W = f := by
  have hc := integralCurveChart_rightZero W true
  change integralCurveChart W 1 ≫ integralCurveRightZero W = _ at hc
  have hi : (f ≫ smoothProductRightZero W) ≫ (smoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W false).toRingHom)) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [Category.assoc, smoothProductRightZero_inclusion, ← Category.assoc, h]
    simp only [Category.assoc]
    rw [hc]
    change g ≫ infinityIdentityInclusion W false ≫
      Spec.map (CommRingCat.ofHom (infinityIdentityInput W false).toRingHom) ≫ _ = _
    rw [← Category.assoc (infinityIdentityInclusion W false),
      ← infinityIdentitySpec_inputs]
    simp only [Category.assoc]
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  have he := smoothCurveAddition_originalInfinity W
    (f ≫ smoothProductRightZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W false).toRingHom)) hi
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (infinityIdentityMap W false).toRingHom)), infinityIdentitySpec_addition] at he
  simpa only [Category.assoc, h] using he

end FLT.Mazur.WeierstrassIntegralChart
