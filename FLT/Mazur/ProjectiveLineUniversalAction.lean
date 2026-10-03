/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveLineProductOverlap
public import FLT.Mazur.PolygonUniversalScaling
public import FLT.Mazur.ProjectiveLineEndpoints
/-!
# Universal scaling of the projective line

Glue the two reciprocal scaling formulas over the Laurent parameter ring.
The resulting morphism has source the actual product with the multiplicative
group, preserves the base map, and fixes zero and infinity as sections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped Polynomial LaurentPolynomial MonoidalCategory
universe u
namespace FLT.Mazur.ProjectiveLineUniversalAction
open ProjectiveLineProductCharts
variable (K : Type u) [Field K]

/-- The Laurent ring carrying the universal unit. -/
abbrev parameter := K[T;T⁻¹]
/-- Multiply the first affine coordinate by the universal unit. -/
def leftMap : Spec (.of (parameter K)[X]) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom PolygonUniversalScaling.scaleLeft)
/-- Multiply the second affine coordinate by the inverse universal unit. -/
def rightMap : Spec (.of (parameter K)[X]) ⟶ ProjectiveLine.chart K :=
  Spec.map (CommRingCat.ofHom PolygonUniversalScaling.scaleRight)
/-- The common scaling on the Laurent intersection. -/
def overlapMap : Spec (.of (parameter K)[T;T⁻¹]) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom PolygonUniversalScaling.overlapScale)

/-- The first chart scaling restricts to the common overlap map. -/
theorem overlap_left : ProjectiveLineProductOverlap.left (parameter K) ≫ leftMap K =
    overlapMap K ≫ ProjectiveLine.overlapLeft K := by
  simpa only [ProjectiveLineProductOverlap.left, leftMap, overlapMap,
    ProjectiveLine.overlapLeft, CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (PolygonUniversalScaling.overlap_left (R := K))

/-- The second chart scaling restricts through reciprocal coordinates. -/
theorem overlap_right : ProjectiveLineProductOverlap.right (parameter K) ≫ rightMap K =
    overlapMap K ≫ ProjectiveLine.overlapRight K := by
  simpa only [ProjectiveLineProductOverlap.right, ProjectiveLineProductOverlap.inversion_hom,
    ProjectiveLineProductOverlap.left, rightMap, overlapMap, ProjectiveLine.overlapRight,
    ProjectiveLine.inversion_hom, ProjectiveLine.overlapLeft, CommRingCat.ofHom_comp,
    Spec.map_comp, Category.assoc] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (PolygonUniversalScaling.overlap_right (R := K))

/-- The universal scaling morphism on the actual fiber product. -/
def action : product K (parameter K) ⟶ ProjectiveLine.scheme K :=
  (ProjectiveLineProductOverlap.isPushout K (parameter K)).desc
    (leftMap K ≫ ProjectiveLine.left K) (rightMap K ≫ ProjectiveLine.right K) (by
      rw [← Category.assoc, overlap_left, Category.assoc, ProjectiveLine.overlap_condition,
        ← Category.assoc, ← overlap_right, Category.assoc])

/-- Restriction of universal scaling to the first product chart. -/
@[reassoc (attr := simp)] theorem left_action :
    productChartMap K (parameter K) false ≫ action K = leftMap K ≫ ProjectiveLine.left K :=
  (ProjectiveLineProductOverlap.isPushout K (parameter K)).inl_desc _ _ _
/-- Restriction of universal scaling to the second product chart. -/
@[reassoc (attr := simp)] theorem right_action :
    productChartMap K (parameter K) true ≫ action K = rightMap K ≫ ProjectiveLine.right K :=
  (ProjectiveLineProductOverlap.isPushout K (parameter K)).inr_desc _ _ _

/-- The first chart scaling preserves coefficient scalars. -/
theorem leftMap_toBase : leftMap K ≫ ProjectiveLine.chartToBase K =
    Spec.map (CommRingCat.ofHom (algebraMap (parameter K) (parameter K)[X])) ≫
      parameterToBase K (parameter K) := by
  have h : (PolygonUniversalScaling.scaleLeft (R := K)).comp Polynomial.C =
      (algebraMap (parameter K) (parameter K)[X]).comp (algebraMap K (parameter K)) := by
    ext r
    simp [PolygonUniversalScaling.scaleLeft]
  simpa only [leftMap, ProjectiveLine.chartToBase, parameterToBase,
    CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h

/-- The second chart scaling preserves coefficient scalars. -/
theorem rightMap_toBase : rightMap K ≫ ProjectiveLine.chartToBase K =
    Spec.map (CommRingCat.ofHom (algebraMap (parameter K) (parameter K)[X])) ≫
      parameterToBase K (parameter K) := by
  have h : (PolygonUniversalScaling.scaleRight (R := K)).comp Polynomial.C =
      (algebraMap (parameter K) (parameter K)[X]).comp (algebraMap K (parameter K)) := by
    ext r
    simp [PolygonUniversalScaling.scaleRight]
  simpa only [rightMap, ProjectiveLine.chartToBase, parameterToBase,
    CommRingCat.ofHom_comp, Spec.map_comp] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h

/-- Universal scaling is a morphism over the base field. -/
@[reassoc] theorem action_toBase : action K ≫ ProjectiveLine.toBase K =
    pullback.fst _ _ ≫ parameterToBase K (parameter K) := by
  apply (ProjectiveLineProductOverlap.isPushout K (parameter K)).hom_ext
  · simp [leftMap_toBase]
  · simp [rightMap_toBase]

/-- Universal projective-line scaling in the over-category. -/
def act : MultiplicativeGroupScheme.gm K ⊗ Over.mk (ProjectiveLine.toBase K) ⟶
    Over.mk (ProjectiveLine.toBase K) := Over.homMk (action K) (action_toBase K)

/-- The constant zero or infinity section over the parameter scheme. -/
def endpoint (b : Bool) : Spec (.of (parameter K)) ⟶ product K (parameter K) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom 0)) ≫
    productChartMap K (parameter K) b

/-- Each endpoint section has identity parameter projection. -/
@[reassoc (attr := simp)] theorem endpoint_fst (b : Bool) :
    endpoint K b ≫ pullback.fst _ _ = 𝟙 _ := by
  rw [endpoint, Category.assoc, productChartMap_fst, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change Polynomial.eval 0 (Polynomial.C r) = r
  simp

/-- The projective-line projection is the chosen constant endpoint. -/
@[reassoc] theorem endpoint_snd (b : Bool) :
    endpoint K b ≫ pullback.snd _ _ = parameterToBase K (parameter K) ≫
      (if b then ProjectiveLine.infinity K else ProjectiveLine.zero K) := by
  have h : (Polynomial.evalRingHom 0 : (parameter K)[X] →+* parameter K).comp
      (Polynomial.mapRingHom (algebraMap K (parameter K))) =
      (algebraMap K (parameter K)).comp (Polynomial.evalRingHom 0) := by
    ext <;> simp
  have he := congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at he
  rw [endpoint, Category.assoc, productChartMap_snd, ← Category.assoc, he]
  cases b <;> simp [parameterToBase, chartCover, ProjectiveLine.zero,
    ProjectiveLine.infinity, ProjectiveLine.chartZero, Category.assoc]

/-- Universal scaling fixes the zero section. -/
@[reassoc] theorem zero_action : endpoint K false ≫ action K =
    parameterToBase K (parameter K) ≫ ProjectiveLine.zero K := by
  have he := congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (PolygonUniversalScaling.scaleLeft_zero (R := K))
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at he
  rw [endpoint, Category.assoc, left_action, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [he]
  rfl

/-- Universal scaling fixes the infinity section. -/
@[reassoc] theorem infinity_action : endpoint K true ≫ action K =
    parameterToBase K (parameter K) ≫ ProjectiveLine.infinity K := by
  have he := congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
    (PolygonUniversalScaling.scaleRight_zero (R := K))
  simp only [CommRingCat.ofHom_comp, Spec.map_comp] at he
  rw [endpoint, Category.assoc, right_action, ← Category.assoc]
  change (Spec.map _ ≫ Spec.map _) ≫ _ = _
  rw [he]
  rfl
end FLT.Mazur.ProjectiveLineUniversalAction
