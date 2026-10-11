/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation

/-!
# Both projections of an evaluated universal Laurent pair

The first unit is the group parameter; the second is the component coordinate
on either projective chart. These identities retain the product factor order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineUniversalAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  (q r : Aˣ)

/-- The first projection of the evaluated pair is exactly its group parameter. -/
@[reassoc] theorem laurentPairEvaluation_fst (b : Bool) :
    Spec.map (CommRingCat.ofHom (laurentPairEvaluation (K := K) q r).toRingHom) ≫
        ProjectiveLineProductOverlap.left K[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap K K[T;T⁻¹] b ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit q).toRingHom) := by
  rw [ProjectiveLineProductCharts.productChartMap_fst]
  simp only [ProjectiveLineProductOverlap.left, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  apply RingHom.ext
  intro t
  simp [laurentPairEvaluation]

/-- Changing the inner Laurent coefficients then evaluating retains the second unit. -/
theorem laurentPairEvaluation_coeff :
    (laurentPairEvaluation (K := K) q r).toRingHom.comp
        (PolygonScalingNaturality.coeffMap (algebraMap K K[T;T⁻¹])) =
      (LaurentUnitPoints.evalUnit r).toRingHom := by
  apply PolygonScalingNaturality.ringHom_ext
  · intro t
    simp [laurentPairEvaluation]
  · simp [laurentPairEvaluation]
  · simp [laurentPairEvaluation]

/-- The second projection is the original component coordinate on the chosen chart. -/
@[reassoc] theorem laurentPairEvaluation_snd (b : Bool) :
    Spec.map (CommRingCat.ofHom (laurentPairEvaluation (K := K) q r).toRingHom) ≫
        ProjectiveLineProductOverlap.left K[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap K K[T;T⁻¹] b ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit r).toRingHom) ≫
        ProjectiveLine.overlapLeft K ≫
          (if b then ProjectiveLine.right K else ProjectiveLine.left K) := by
  rw [ProjectiveLineProductCharts.productChartMap_snd, ← Category.assoc
    (ProjectiveLineProductOverlap.left _), ProjectiveLineProductOverlap.left_coeff]
  simp only [← Category.assoc, ProjectiveLineProductOverlap.coeff, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, laurentPairEvaluation_coeff]
  rfl

end FLT.Mazur.ProjectiveLineUniversalAction
