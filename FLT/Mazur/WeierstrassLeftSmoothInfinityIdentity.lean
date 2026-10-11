/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothOriginalFormulas
public import FLT.Mazur.WeierstrassLeftSmoothZeroGraph
public import FLT.Mazur.WeierstrassInfinityIdentityNeighborhood
public import FLT.Mazur.WeierstrassGlobalAdditionZeroRestrictions

/-!
# Zero fixes the original infinity neighborhood

The regular infinity identity applies on arbitrary common schemes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Zero on the left fixes every presentation in its infinity neighborhood. -/
theorem leftSmoothCurveAddition_leftZero_neighborhood {X : Scheme.{u}}
    (f : X ⟶ integralCurve W)
    (g : X ⟶ Spec (.of (InfinityIdentityOpen W true)))
    (h : f =
      g ≫ infinityIdentityInclusion W true ≫ integralCurveChart W 1) :
    f ≫ leftSmoothProductZero W ≫ leftSmoothCurveAddition W = f := by
  have hc := integralCurveChart_leftZero W true
  change integralCurveChart W 1 ≫ integralCurveLeftZero W = _ at hc
  have hi : (f ≫ leftSmoothProductZero W) ≫ (leftSmoothCurveProductOpen W).ι =
      (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W true).toRingHom)) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
    rw [Category.assoc, leftSmoothProductZero_inclusion, h]
    simp only [Category.assoc]
    rw [hc]
    change g ≫ infinityIdentityInclusion W true ≫
      Spec.map (CommRingCat.ofHom (infinityIdentityInput W true).toRingHom) ≫ _ = _
    rw [← Category.assoc (infinityIdentityInclusion W true),
      ← infinityIdentitySpec_inputs]
    simp only [Category.assoc]
  have he := leftSmoothCurveAddition_originalInfinity W
    (f ≫ leftSmoothProductZero W)
    (g ≫ Spec.map (CommRingCat.ofHom (infinityIdentityMap W true).toRingHom)) hi
  simp only [Category.assoc] at he
  rw [← Category.assoc (Spec.map (CommRingCat.ofHom
    (infinityIdentityMap W true).toRingHom)), infinityIdentitySpec_addition] at he
  simpa only [Category.assoc, h] using he

end FLT.Mazur.WeierstrassIntegralChart
