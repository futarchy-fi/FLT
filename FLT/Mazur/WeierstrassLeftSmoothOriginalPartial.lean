/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothOriginalFormulas

/-!
# The enlarged global law retains the original partial affine law

Every actual partial affine presentation computes translation on the original
cubic, including singular second inputs and arbitrary common source schemes.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A partial affine presentation of a left smooth pair retains its original output. -/
theorem leftSmoothCurveAddition_originalPartial {X : Scheme.{u}}
    (f : X ⟶ (leftSmoothCurveProductOpen W).toScheme)
    (g : X ⟶ (affineAdditionDomain W).toScheme)
    (h : f ≫ (leftSmoothCurveProductOpen W).ι =
      g ≫ (affineAdditionDomain W).ι ≫ integralCurveProductChart W false false) :
    f ≫ leftSmoothCurveAddition W = g ≫ affinePartialAddition W := by
  have hs : Set.range (g ≫ (affineAdditionDomain W).ι) ⊆ leftSmoothAffineInputOpen W := by
    rintro _ ⟨p, rfl⟩
    apply (leftSmoothProductChartOpen_affine W).le
    change ((g ≫ (affineAdditionDomain W).ι) ≫
      integralCurveProductChart W false false) p ∈ leftSmoothCurveProductOpen W
    rw [Category.assoc, ← h]
    exact (f p).property
  let a := IsOpenImmersion.lift (leftSmoothAffineInputOpen W).ι
    (g ≫ (affineAdditionDomain W).ι) (by rw [Scheme.Opens.range_ι]; exact hs)
  have ha : a ≫ (leftSmoothAffineInputOpen W).ι = g ≫ (affineAdditionDomain W).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have he : a ≫ leftSmoothAffineInputToDomain W = g := by
    apply (cancel_mono (affineAdditionDomain W).ι).mp
    rw [Category.assoc, leftSmoothAffineInputToDomain_inclusion]
    exact ha
  rw [leftSmoothCurveAddition_originalAffine W f a
    (by rw [← Category.assoc, ha, Category.assoc]; exact h),
    leftSmoothAffineAddition, ← Category.assoc, he]

end FLT.Mazur.WeierstrassIntegralChart
