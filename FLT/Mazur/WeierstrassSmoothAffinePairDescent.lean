/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFormulaComparison
public import FLT.Mazur.WeierstrassAffinePairDescent

/-!
# Descent through the addition charts of an actual smooth affine pair

An affine presentation of a categorical smooth pair lies in the smooth input
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

/-- An affine presentation of a smooth pair factors through the smooth affine open. -/
theorem exists_smoothAffinePair_of_presentation {X : Scheme.{u}}
    (p : X ⟶ smoothFactorProduct W) (a : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false = p ≫ smoothFactorsInclusion W) :
    ∃ b : X ⟶ (smoothAffineInputOpen W).toScheme, b ≫ (smoothAffineInputOpen W).ι = a := by
  have hs : Set.range a ⊆ smoothAffineInputOpen W := by
    rintro _ ⟨x, rfl⟩
    apply (smoothProductChartOpen_affine W).le
    change (a ≫ integralCurveProductChart W false false) x ∈ smoothCurveProductOpen W
    rw [ha, ← smoothFactorsToProduct_inclusion, ← Category.assoc]
    exact ((p ≫ smoothFactorsToProduct W) x).property
  exact ⟨IsOpenImmersion.lift (smoothAffineInputOpen W).ι a
    (by rw [Scheme.Opens.range_ι]; exact hs), IsOpenImmersion.lift_fac _ _ _⟩

/-- The original four addition charts detect equality over an actual smooth affine pair. -/
theorem smoothAffinePair_hom_ext {X Y : Scheme.{u}}
    (p : X ⟶ smoothFactorProduct W) (a : X ⟶ Spec (.of (AffineProduct W)))
    (ha : a ≫ integralCurveProductChart W false false = p ≫ smoothFactorsInclusion W)
    (f g : X ⟶ Y)
    (h : ∀ (i : AdditionChartIndex) (Z : Scheme.{u}) (u : Z ⟶ X)
      (b : Z ⟶ Spec (additionChartRing W i)),
      b ≫ additionChartInclusion W i = u ≫ a → u ≫ f = u ≫ g) : f = g := by
  obtain ⟨q, hq⟩ := exists_smoothAffinePair_of_presentation W p a ha
  let C := smoothAffineAdditionCover W
  apply Scheme.Cover.hom_ext (C.pullback₁ q)
  intro i
  let u := (C.pullback₁ q).f i
  let v := Scheme.Cover.pullbackHom C q i
  apply h i _ u (v ≫ smoothAffineAdditionProjection W i)
  rw [Category.assoc, smoothAffineAdditionProjection_inputs, ← Category.assoc]
  change (Scheme.Cover.pullbackHom C q i ≫ C.f i) ≫ _ = _
  rw [Scheme.Cover.pullbackHom_map, Category.assoc, hq]

end FLT.Mazur.WeierstrassIntegralChart
