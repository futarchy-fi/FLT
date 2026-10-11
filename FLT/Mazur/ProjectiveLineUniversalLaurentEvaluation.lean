/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineUniversalAction
public import FLT.Mazur.LaurentUnitPoints

/-!
# Evaluate universal projective scaling at two independent units

The outer Laurent coordinate is the action parameter and the inner one is
the component coordinate. Evaluation of the actual universal action on its
punctured first chart multiplies those two units.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineUniversalAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- Evaluate the outer action parameter and the inner component parameter independently. -/
def laurentPairEvaluation (q r : Aˣ) : K[T;T⁻¹][T;T⁻¹] →ₐ[K] A :=
  { LaurentPolynomial.eval₂ (LaurentUnitPoints.evalUnit q).toRingHom r with
    commutes' := fun k => by
      change LaurentPolynomial.eval₂ _ r (LaurentPolynomial.C (LaurentPolynomial.C k)) = _
      rw [LaurentPolynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        LaurentUnitPoints.evalUnit_C] }

/-- Universal overlap scaling preserves the ground-field algebra structure. -/
def overlapAlgebra : K[T;T⁻¹] →ₐ[K] K[T;T⁻¹][T;T⁻¹] :=
  { PolygonUniversalScaling.overlapScale with
    commutes' := fun k => PolygonUniversalScaling.overlapScale_C k }

/-- Evaluation of the actual overlap scaling is multiplication of its two units. -/
theorem laurentPairEvaluation_overlap (q r : Aˣ) :
    (laurentPairEvaluation (K := K) q r).comp overlapAlgebra =
      LaurentUnitPoints.evalUnit (q * r) := by
  apply LaurentUnitPoints.hom_ext
  · simp [laurentPairEvaluation, overlapAlgebra, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit]
  · simp [laurentPairEvaluation, overlapAlgebra, PolygonUniversalScaling.u,
      PolygonChartScaling.coordinateUnit]
    ring

/-- The universal projective action on the evaluated torus is its actual product coordinate. -/
theorem laurentPairEvaluation_action (q r : Aˣ) :
    Spec.map (CommRingCat.ofHom (laurentPairEvaluation (K := K) q r).toRingHom) ≫
        ProjectiveLineProductOverlap.left K[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap K K[T;T⁻¹] false ≫ action K =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (q * r)).toRingHom) ≫
        ProjectiveLine.overlapLeft K ≫ ProjectiveLine.left K := by
  rw [left_action, ← Category.assoc (ProjectiveLineProductOverlap.left _),
    overlap_left, Category.assoc, ← Category.assoc]
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f)))
    (laurentPairEvaluation_overlap (K := K) q r)
  change Spec.map _ = _ at h
  rw [show Spec.map (CommRingCat.ofHom
      (((laurentPairEvaluation (K := K) q r).comp overlapAlgebra).toRingHom)) =
      Spec.map (CommRingCat.ofHom (laurentPairEvaluation (K := K) q r).toRingHom) ≫ overlapMap K by
        rw [overlapMap, ← Spec.map_comp]; rfl] at h
  rw [h]

/-- On the other affine chart, universal scaling uses the inverse action parameter. -/
theorem laurentPairEvaluation_right (q r : Aˣ) :
    ((laurentPairEvaluation (K := K) q r).toRingHom.comp Polynomial.toLaurent).comp
        PolygonUniversalScaling.scaleRight =
      (LaurentUnitPoints.evalUnit (q⁻¹ * r)).toRingHom.comp Polynomial.toLaurent := by
  ext <;> simp [laurentPairEvaluation, PolygonUniversalScaling.scaleRight,
    PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

/-- The actual right-chart action evaluates to the inverse cyclic character. -/
theorem laurentPairEvaluation_right_action (q r : Aˣ) :
    Spec.map (CommRingCat.ofHom (laurentPairEvaluation (K := K) q r).toRingHom) ≫
        ProjectiveLineProductOverlap.left K[T;T⁻¹] ≫
        ProjectiveLineProductCharts.productChartMap K K[T;T⁻¹] true ≫ action K =
      Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (q⁻¹ * r)).toRingHom) ≫
        ProjectiveLine.overlapLeft K ≫ ProjectiveLine.right K := by
  rw [right_action]
  have h := congrArg (fun f => Spec.map (CommRingCat.ofHom f) ≫ ProjectiveLine.right K)
    (laurentPairEvaluation_right (K := K) q r)
  simpa only [ProjectiveLineProductOverlap.left, rightMap, ProjectiveLine.overlapLeft,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc] using h

end FLT.Mazur.ProjectiveLineUniversalAction
