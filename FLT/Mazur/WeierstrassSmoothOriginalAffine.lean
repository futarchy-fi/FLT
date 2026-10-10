/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAdditionOriginalFormulas
public import FLT.Mazur.WeierstrassNegationAdditionDescent

/-!
# Retaining the partial affine law and its inverse calculation

The full smooth law agrees with the original partial affine addition on any
common scheme. Its inverse calculation descends on the actual formula domain,
without a good reduction hypothesis.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The full smooth addition retains the smooth affine formula on arbitrary inputs. -/
theorem smoothCurveAddition_originalAffine {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (a : X ⟶ (smoothAffineInputOpen W).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι =
      a ≫ (smoothAffineInputOpen W).ι ≫ integralCurveProductChart W false false) :
    f ≫ smoothCurveAddition W = a ≫ smoothAffineAddition W := by
  let g := a ≫ (smoothAffineInputOpen W).ι
  have hg : g ≫ integralCurveProductChart W false false =
      f ≫ (smoothCurveProductOpen W).ι := by
    simpa only [g, Category.assoc] using h.symm
  let l := smoothProductChartLift W false false f g hg
  have hl : l ≫ smoothProductChartInput W false false =
      f ≫ (smoothCurveProductOpen W).ι := by
    rw [smoothProductChartInput, ← Category.assoc]
    exact (congrArg (fun q => q ≫ integralCurveProductChart W false false)
      (IsOpenImmersion.lift_fac _ _ _)).trans hg
  rw [smoothCurveAddition_commonScheme W false false f l hl.symm]
  exact smoothInputAddition_commonAffine W false false l a (hl.trans h)

/-- A partial affine presentation of a smooth pair retains its original output. -/
theorem smoothCurveAddition_originalPartial {X : Scheme.{u}}
    (f : X ⟶ (smoothCurveProductOpen W).toScheme)
    (g : X ⟶ (affineAdditionDomain W).toScheme)
    (h : f ≫ (smoothCurveProductOpen W).ι =
      g ≫ (affineAdditionDomain W).ι ≫ integralCurveProductChart W false false) :
    f ≫ smoothCurveAddition W ≫ (integralSmoothOpen W).ι = g ≫ affinePartialAddition W := by
  have hs : Set.range (g ≫ (affineAdditionDomain W).ι) ⊆ smoothAffineInputOpen W := by
    rintro _ ⟨p, rfl⟩
    apply (smoothProductChartOpen_affine W).le
    change ((g ≫ (affineAdditionDomain W).ι) ≫
      integralCurveProductChart W false false) p ∈ smoothCurveProductOpen W
    rw [Category.assoc, ← h]
    exact (f p).property
  let a := IsOpenImmersion.lift (smoothAffineInputOpen W).ι
    (g ≫ (affineAdditionDomain W).ι) (by rw [Scheme.Opens.range_ι]; exact hs)
  have ha : a ≫ (smoothAffineInputOpen W).ι = g ≫ (affineAdditionDomain W).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have he : a ≫ smoothAffineInputToDomain W = g := by
    apply (cancel_mono (affineAdditionDomain W).ι).mp
    rw [Category.assoc, smoothAffineInputToDomain_inclusion]
    exact ha
  rw [← Category.assoc, smoothCurveAddition_originalAffine W f a
    (by rw [← Category.assoc, ha, Category.assoc]; exact h),
    Category.assoc, smoothAffineAddition_partial, ← Category.assoc, he]

/-- Partial affine addition sends every actual point-negation pair in its domain to zero. -/
theorem affinePartialAddition_negation_commonScheme {X : Scheme.{u}}
    (f : X ⟶ (affineAdditionDomain W).toScheme) (g : X ⟶ chartScheme W 2)
    (h : f ≫ (affineAdditionDomain W).ι =
      g ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom)) :
    f ≫ affinePartialAddition W =
      g ≫ chartStructure W 2 ≫ integralCurveZero W := by
  let C := affineAdditionDomainCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ f)
  intro i
  let p := (C.pullback₁ f).f i
  let q := Scheme.Cover.pullbackHom C f i
  have hi : p ≫ f = q ≫ additionChartToDomain W i :=
    (Scheme.Cover.pullbackHom_map C f i).symm
  have hh : q ≫ additionChartInclusion W i =
      (p ≫ g) ≫ Spec.map (CommRingCat.ofHom (affineNegationPair W).toRingHom) := by
    rw [← additionChartToDomain_inclusion, ← Category.assoc, ← hi, Category.assoc, h,
      ← Category.assoc]
  change p ≫ (f ≫ affinePartialAddition W) = p ≫ _
  rw [← Category.assoc, hi, Category.assoc, additionChartToDomain_addition]
  simpa only [Category.assoc, chartStructure] using additionNegation_commonScheme W i q _ hh

end FLT.Mazur.WeierstrassIntegralChart
