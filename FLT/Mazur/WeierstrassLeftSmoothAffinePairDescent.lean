/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassLeftSmoothFormulaComparison
public import FLT.Mazur.WeierstrassAffinePairDescent

/-!
# Descent through the addition charts of an actual left smooth affine pair

An affine presentation of a categorical left smooth pair lies in the smooth input
open. The pulled-back four-chart cover therefore detects morphism equality
without any condition on the discriminant.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- An affine presentation of a left smooth pair factors through the smooth affine open. -/
theorem exists_leftSmoothAffinePair_of_presentation {X : Scheme.{u}}
    (p : X ⟶ leftSmoothFactorProduct W) (a : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false = p ≫ leftSmoothFactorsInclusion W) :
    ∃ b : X ⟶ (leftSmoothAffineInputOpen W).toScheme, b ≫ (leftSmoothAffineInputOpen W).ι = a := by
  have hs : Set.range a ⊆ leftSmoothAffineInputOpen W := by
    rintro _ ⟨x, rfl⟩
    apply (leftSmoothProductChartOpen_affine W).le
    change (a ≫ integralCurveProductChart W false false) x ∈ leftSmoothCurveProductOpen W
    rw [ha, ← leftSmoothFactorsToProduct_inclusion, ← Category.assoc]
    exact ((p ≫ leftSmoothFactorsToProduct W) x).property
  exact ⟨IsOpenImmersion.lift (leftSmoothAffineInputOpen W).ι a
    (by rw [Scheme.Opens.range_ι]; exact hs), IsOpenImmersion.lift_fac _ _ _⟩

/-- The original four addition charts detect equality over an actual left smooth affine pair. -/
theorem leftSmoothAffinePair_hom_ext {X Y : Scheme.{u}}
    (p : X ⟶ leftSmoothFactorProduct W) (a : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false = p ≫ leftSmoothFactorsInclusion W)
    (f g : X ⟶ Y)
    (h : ∀ (i : AdditionChartIndex) (Z : Scheme.{u}) (u : Z ⟶ X)
      (b : Z ⟶ Spec (additionChartRing W i)),
      b ≫ additionChartInclusion W i = u ≫ a → u ≫ f = u ≫ g) : f = g := by
  obtain ⟨q, hq⟩ := exists_leftSmoothAffinePair_of_presentation W p a ha
  let C := leftSmoothAffineAdditionCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ q)
  intro i
  let u := (C.pullback₁ q).f i
  let v := Scheme.Cover.pullbackHom C q i
  apply h i _ u (v ≫ leftSmoothAffineAdditionProjection W i)
  rw [Category.assoc, leftSmoothAffineAdditionProjection_inputs, ← Category.assoc]
  change (Scheme.Cover.pullbackHom C q i ≫ C.f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc, hq]

end FLT.Mazur.WeierstrassIntegralChart
