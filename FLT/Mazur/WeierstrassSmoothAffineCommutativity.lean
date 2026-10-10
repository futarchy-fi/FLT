/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothOriginalAffine
public import FLT.Mazur.WeierstrassSmoothInputSwap
public import FLT.Mazur.WeierstrassAffineAdditionSwapDescent

/-!
# Commutativity on every smooth affine pair

The original reversed-input formula comparisons descend to the partial
addition domain and then to all smooth affine inputs, including bad fibers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A partial affine presentation agrees with every reversed original formula. -/
theorem affinePartialAddition_swap_chart (j : AdditionChartIndex) {X : Scheme.{u}}
    (f : X ⟶ (affineAdditionDomain W).toScheme)
    (g : X ⟶ Spec (additionChartRing W j))
    (h : f ≫ (affineAdditionDomain W).ι =
      g ≫ additionChartInclusion W j ≫ affineInputSwap W) :
    f ≫ affinePartialAddition W = g ≫ additionCurveChart W j := by
  let C := affineAdditionDomainCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ f)
  intro i
  let p := (C.pullback₁ f).f i
  let q := Scheme.Cover.pullbackHom C f i
  have hi : p ≫ f = q ≫ additionChartToDomain W i :=
    (Scheme.Cover.pullbackHom_map C f i).symm
  have hh : q ≫ additionChartInclusion W i =
      (p ≫ g) ≫ additionChartInclusion W j ≫ affineInputSwap W := by
    rw [← additionChartToDomain_inclusion, ← Category.assoc, ← hi, Category.assoc, h]
    simp only [Category.assoc]
  change p ≫ (f ≫ affinePartialAddition W) = p ≫ _
  rw [← Category.assoc, hi, Category.assoc, additionChartToDomain_addition]
  simpa only [Category.assoc] using additionCurveChart_swap_commonScheme W i j q _ hh

/-- Partial affine addition agrees on all common reversed-input presentations. -/
theorem affinePartialAddition_swap_commonScheme {X : Scheme.{u}}
    (f g : X ⟶ (affineAdditionDomain W).toScheme)
    (h : f ≫ (affineAdditionDomain W).ι =
      g ≫ (affineAdditionDomain W).ι ≫ affineInputSwap W) :
    f ≫ affinePartialAddition W = g ≫ affinePartialAddition W := by
  let C := affineAdditionDomainCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ g)
  intro j
  let p := (C.pullback₁ g).f j
  let q := Scheme.Cover.pullbackHom C g j
  have hi : p ≫ g = q ≫ additionChartToDomain W j :=
    (Scheme.Cover.pullbackHom_map C g j).symm
  have hh : (p ≫ f) ≫ (affineAdditionDomain W).ι =
      q ≫ additionChartInclusion W j ≫ affineInputSwap W := by
    rw [Category.assoc, h, ← Category.assoc p g, hi, Category.assoc,
      additionChartToDomain_inclusion_assoc]
  change p ≫ (f ≫ affinePartialAddition W) = p ≫ (g ≫ affinePartialAddition W)
  rw [← Category.assoc p g, hi, Category.assoc, additionChartToDomain_addition]
  simpa only [Category.assoc] using affinePartialAddition_swap_chart W j (p ≫ f) q hh

/-- Smooth affine addition is symmetric over every coefficient base. -/
@[reassoc] theorem smoothAffineAddition_swap :
    smoothAffineSwap W ≫ smoothAffineAddition W = smoothAffineAddition W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  simp only [Category.assoc, smoothAffineAddition_partial]
  rw [← Category.assoc]
  apply affinePartialAddition_swap_commonScheme W
  rw [Category.assoc, smoothAffineInputToDomain_inclusion,
    smoothAffineSwap_inclusion, smoothAffineInputToDomain_inclusion_assoc]

/-- The full smooth law is symmetric on every common smooth affine presentation. -/
theorem smoothCurveAddition_swap_affine {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (a : X ⟶ (smoothAffineInputOpen W).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι =
      a ≫ (smoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ smoothProductSwap W ≫ smoothCurveAddition W = f ≫ smoothCurveAddition W := by
  have hs : affineInputSwap W ≫ integralCurveProductChart W false false =
      integralCurveProductChart W false false ≫ integralCurveSwap W :=
    (integralCurveProductChart_swap W false false).symm
  have hi : (f ≫ smoothProductSwap W) ≫ (smoothCurveProductOpen W).ι =
      (a ≫ smoothAffineSwap W) ≫ (smoothAffineInputOpen W).ι ≫
        integralCurveProductChart W false false := by
    rw [Category.assoc, smoothProductSwap_inclusion, ← Category.assoc, h]
    simp only [Category.assoc, smoothAffineSwap_inclusion_assoc]
    rw [hs]
  rw [← Category.assoc, smoothCurveAddition_originalAffine W _ _ hi,
    Category.assoc, smoothAffineAddition_swap, smoothCurveAddition_originalAffine W f a h]

end FLT.Mazur.WeierstrassIntegralChart
