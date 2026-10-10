/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineInputFactorization

/-!
# Descent through the four affine-input addition charts

Equality over an affine pair can be checked on its four genuine addition opens.
A pair whose two global projections have affine presentations factors through
the actual affine product, using the tensor-product pullback property.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Check any equality after pulling back the four affine-input addition domains. -/
theorem affinePair_hom_ext (hΔ : IsUnit W.Δ) {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of (AffineProduct W))) (f g : X ⟶ Y)
    (h : ∀ (i : AdditionChartIndex) (Z : Scheme.{u}) (a : Z ⟶ X)
      (b : Z ⟶ Spec (additionChartRing W i)),
      b ≫ additionChartInclusion W i = a ≫ p → a ≫ f = a ≫ g) : f = g := by
  let C := additionAffineOpenCover W hΔ
  apply Scheme.Cover.hom_ext (C.pullback₁ p)
  intro i
  exact h i _ ((C.pullback₁ p).f i) (Scheme.Cover.pullbackHom C p i)
    (Scheme.Cover.pullbackHom_map C p i)

/-- Two affine input presentations determine a lift of the original global pair. -/
theorem exists_affinePair_of_projections {X : Scheme.{u}}
    (p : X ⟶ integralCurveProduct W) (f g : X ⟶ chartScheme W 2)
    (hf : f ≫ integralCurveChart W 2 = p ≫ pullback.fst _ _)
    (hg : g ≫ integralCurveChart W 2 = p ≫ pullback.snd _ _) :
    ∃ a : X ⟶ Spec (.of (AffineProduct W)),
      a ≫ integralCurveProductChart W false false = p := by
  have hbase : f ≫ chartStructure W 2 = g ≫ chartStructure W 2 := by
    rw [← integralCurveChart_structure, ← Category.assoc, hf, Category.assoc,
      pullback.condition, ← Category.assoc, ← hg, Category.assoc,
      integralCurveChart_structure]
  obtain ⟨a, ha, ha'⟩ :=
    (tensorSpecIsPullback R (Coordinate W 2) (Coordinate W 2)).exists_lift f g hbase
  refine ⟨a, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, integralCurveProductChart_fst, ← Category.assoc]
    exact (congrArg (fun x => x ≫ integralCurveChart W 2) ha).trans hf
  · rw [Category.assoc, integralCurveProductChart_snd, ← Category.assoc]
    exact (congrArg (fun x => x ≫ integralCurveChart W 2) ha').trans hg

end FLT.Mazur.WeierstrassIntegralChart
