/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothAffineCover

/-!
# Addition on all smooth affine pairs in arbitrary reduction

Glue the four restricted original formulas. The resulting morphism lands in
the full relative smooth curve and agrees with the original partial addition,
without imposing a unit discriminant on the coefficient equation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Smooth addition on one member of the pulled-back four-chart cover. -/
def smoothAffineAdditionLocal (i : AdditionChartIndex) :
    (smoothAffineAdditionCover W).X i ⟶ (integralSmoothOpen W).toScheme :=
  smoothAffineAdditionLift W i ≫ additionSmoothChart W i

/-- The pulled-back smooth formulas agree on every common input scheme. -/
theorem smoothAffineAdditionLocal_commonScheme (i j : AdditionChartIndex)
    {X : Scheme.{u}} (f : X ⟶ (smoothAffineAdditionCover W).X i)
    (g : X ⟶ (smoothAffineAdditionCover W).X j)
    (h : f ≫ (smoothAffineAdditionCover W).f i =
      g ≫ (smoothAffineAdditionCover W).f j) :
    f ≫ smoothAffineAdditionLocal W i = g ≫ smoothAffineAdditionLocal W j := by
  change f ≫ (smoothAffineAdditionLift W i ≫ additionSmoothChart W i) =
    g ≫ (smoothAffineAdditionLift W j ≫ additionSmoothChart W j)
  rw [← Category.assoc, ← Category.assoc]
  apply additionSmoothChart_commonScheme W i j
  simp only [Category.assoc, smoothAffineAdditionLift_inputs]
  exact congrArg (fun t => t ≫ (smoothAffineInputOpen W).ι) h

/-- The four smooth local formulas agree on their scheme-theoretic overlaps. -/
theorem smoothAffineAdditionLocal_overlap (i j : AdditionChartIndex) :
    pullback.fst ((smoothAffineAdditionCover W).f i) ((smoothAffineAdditionCover W).f j) ≫
        smoothAffineAdditionLocal W i =
      pullback.snd ((smoothAffineAdditionCover W).f i) ((smoothAffineAdditionCover W).f j) ≫
        smoothAffineAdditionLocal W j :=
  smoothAffineAdditionLocal_commonScheme W i j _ _ pullback.condition

/-- The regular addition law on the entire smooth affine input open. -/
def smoothAffineAddition :
    (smoothAffineInputOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme :=
  (smoothAffineAdditionCover W).glueMorphisms (smoothAffineAdditionLocal W)
    (smoothAffineAdditionLocal_overlap W)

/-- The glued smooth law retains each original restricted formula. -/
@[reassoc] theorem smoothAffineAdditionLocal_glued (i : AdditionChartIndex) :
    (smoothAffineAdditionCover W).f i ≫ smoothAffineAddition W =
      smoothAffineAdditionLocal W i :=
  (smoothAffineAdditionCover W).ι_glueMorphisms _ _ i

/-- On the integral curve the smooth law is exactly the original partial addition. -/
@[reassoc] theorem smoothAffineAddition_partial :
    smoothAffineAddition W ≫ (integralSmoothOpen W).ι =
      smoothAffineInputToDomain W ≫ affinePartialAddition W := by
  apply (smoothAffineAdditionCover W).hom_ext
  intro i
  rw [← Category.assoc, smoothAffineAdditionLocal_glued]
  change (smoothAffineAdditionLift W i ≫ additionSmoothChart W i) ≫ _ = _
  rw [Category.assoc, additionSmoothChart_partial,
    smoothAffineAdditionLift_inclusion_assoc]
  have h := Scheme.Cover.pullbackHom_map (affineAdditionDomainCover W)
    (smoothAffineInputToDomain W) i
  change smoothAffineAdditionProjection W i ≫ additionChartToDomain W i =
    (smoothAffineAdditionCover W).f i ≫ smoothAffineInputToDomain W at h
  rw [← Category.assoc, h, Category.assoc]

/-- Smooth affine addition is a morphism over the original coefficient spectrum. -/
theorem smoothAffineAddition_structure :
    smoothAffineAddition W ≫ integralSmoothStructure W =
      (smoothAffineInputOpen W).ι ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AffineProduct W))) := by
  rw [integralSmoothStructure, smoothAffineAddition_partial_assoc,
    affinePartialAddition_structure, smoothAffineInputToDomain_inclusion_assoc]

/-- The local smooth formulas uniquely determine their global smooth affine law. -/
theorem smoothAffineAddition_unique
    (f : (smoothAffineInputOpen W).toScheme ⟶ (integralSmoothOpen W).toScheme)
    (hf : ∀ i, (smoothAffineAdditionCover W).f i ≫ f = smoothAffineAdditionLocal W i) :
    f = smoothAffineAddition W := by
  apply (smoothAffineAdditionCover W).hom_ext
  intro i
  exact (hf i).trans (smoothAffineAdditionLocal_glued W i).symm

end FLT.Mazur.WeierstrassIntegralChart
