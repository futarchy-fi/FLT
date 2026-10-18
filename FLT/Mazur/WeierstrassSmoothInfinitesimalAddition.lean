/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassSmoothInfinitesimalPoints

/-!
# Addition in the full smooth infinitesimal group

The actual smooth group law adds the square-zero X parameters. The comparison
uses the original infinity addition formula, without a good-reduction assumption.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- The actual pair of smooth points in the smooth product open. -/
def smoothInfinitesimalPair (x y : I) :
    Spec (.of A) ⟶ (smoothCurveProductOpen W).toScheme :=
  pullback.lift (f := integralSmoothStructure W) (g := integralSmoothStructure W)
    (smoothInfinitesimalPoint W I hI x).left
    (smoothInfinitesimalPoint W I hI y).left
    ((smoothInfinitesimalPoint W I hI x).w.trans
      (smoothInfinitesimalPoint W I hI y).w.symm) ≫ smoothFactorsToProduct W

/-- The smooth pair retains the original tensor-chart evaluation. -/
theorem smoothInfinitesimalPair_inclusion (x y : I) :
    smoothInfinitesimalPair W I hI x y ≫ (smoothCurveProductOpen W).ι =
      Spec.map (CommRingCat.ofHom (infinitesimalPairEvaluation W I hI x y).toRingHom) ≫
        integralCurveProductChart W true true := by
  rw [smoothInfinitesimalPair, Category.assoc, smoothFactorsToProduct_inclusion]
  apply pullback.hom_ext
  · simp only [Category.assoc, smoothFactorsInclusion, pullback.lift_fst,
      integralCurveProductChart_fst, productChartCoordinate]
    rw [← Category.assoc, pullback.lift_fst, smoothInfinitesimalPoint_inclusion,
      ← Category.assoc, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((infinitesimalPairEvaluation W I hI x y).comp (chartProductLeft W 1 1)).toRingHom) ≫ _
    rw [infinitesimalPairEvaluation, chartProductEvaluation_left]
    rfl
  · simp only [Category.assoc, smoothFactorsInclusion, pullback.lift_snd,
      integralCurveProductChart_snd, productChartCoordinate]
    rw [← Category.assoc, pullback.lift_snd, smoothInfinitesimalPoint_inclusion,
      ← Category.assoc, ← Spec.map_comp]
    change _ = Spec.map (CommRingCat.ofHom
      ((infinitesimalPairEvaluation W I hI x y).comp (chartProductRight W 1 1)).toRingHom) ≫ _
    rw [infinitesimalPairEvaluation, chartProductEvaluation_right]
    rfl

/-- The infinity localization retains the original pair of infinitesimal parameters. -/
theorem smoothInfinitesimalPair_infinity (x y : I) :
    smoothInfinitesimalPair W I hI x y ≫ (smoothCurveProductOpen W).ι =
      Spec.map (CommRingCat.ofHom (infinitesimalAdditionLift W I hI x y).toRingHom) ≫
        infinityAdditionInclusion W ≫ integralCurveProductChart W true true := by
  have hl : Spec.map (CommRingCat.ofHom
      (infinitesimalPairEvaluation W I hI x y).toRingHom) =
      Spec.map (CommRingCat.ofHom (infinitesimalAdditionLift W I hI x y).toRingHom) ≫
        infinityAdditionInclusion W := by
    rw [infinityAdditionInclusion, ← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom
      (infinitesimalPairEvaluation W I hI x y).toRingHom) =
      Spec.map (CommRingCat.ofHom
        ((infinitesimalAdditionLift W I hI x y).comp
          (infinityAdditionRestriction W)).toRingHom)
    rw [infinitesimalAdditionLift_restriction]
  rw [smoothInfinitesimalPair_inclusion, hl, Category.assoc]

/-- The full smooth-group multiplication adds square-zero parameters. -/
theorem smoothInfinitesimalPoint_add (x y : I) :
    smoothInfinitesimalPoint W I hI (x + y) =
      smoothInfinitesimalPoint W I hI x * smoothInfinitesimalPoint W I hI y := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  change _ = (pullback.lift (smoothInfinitesimalPoint W I hI x).left
    (smoothInfinitesimalPoint W I hI y).left
    ((smoothInfinitesimalPoint W I hI x).w.trans
      (smoothInfinitesimalPoint W I hI y).w.symm) ≫ smoothFactorAddition W) ≫ _
  rw [smoothFactorAddition, ← Category.assoc, Category.assoc]
  change _ = smoothInfinitesimalPair W I hI x y ≫ smoothCurveAddition W ≫ _
  rw [smoothCurveAddition_originalInfinity W _ _ (smoothInfinitesimalPair_infinity W I hI x y),
    smoothInfinitesimalPoint_inclusion, infinityAdditionSpec, ← Category.assoc, ← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom
    ((infinitesimalAdditionLift W I hI x y).comp (infinityAdditionChart W)).toRingHom) ≫ _
  rw [infinityAdditionChart_infinitesimal]

/-- The infinitesimal ideal embeds additively in the actual smooth group. -/
def smoothInfinitesimalPointAddHom : I →+
    Additive (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))) ⟶
      (integralSmoothGroup W).X) :=
  AddMonoidHom.mk' (fun x ↦ Additive.ofMul (smoothInfinitesimalPoint W I hI x))
    (smoothInfinitesimalPoint_add W I hI)

end FLT.Mazur.WeierstrassIntegralChart
