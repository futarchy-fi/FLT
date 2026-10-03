/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonNormalizationCoordinates
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# Normalization of the glued one-gon

The two standard projective charts map to the glued one-gon. On each chart
we use D(X) and D(X-1), so the smooth point with coordinate one is included.
Zero and infinity both map to the origin of the equalizer chart.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

universe u

namespace FLT.Mazur.OneGonNormalization

open OneGonTransition OneGonAffineCover OneGonNormalizationCoordinates PolygonNodePresentation

variable (K : Type u) [Field K]

/-- Compatibility of the left normalization formula with the torus chart. -/
theorem left_condition : toLaurent K ≫ OneGonGluing.torus K =
    toOne K ≫ leftPatch K ≫ OneGonGluing.node K := by
  rw [toOne_leftPatch_assoc, OneGonGluing.overlap_condition,
    ← Category.assoc, transition_toTorus]

/-- Compatibility of the right normalization formula with the torus chart. -/
theorem right_condition :
    toLaurent K ≫ (ProjectiveLine.inversion K).hom ≫ OneGonGluing.torus K =
      toOne K ≫ rightPatch K ≫ OneGonGluing.node K := by
  rw [toOne_rightPatch_assoc, OneGonGluing.overlap_condition,
    rightTransition_toTorus_assoc]

/-- Normalization on the standard chart containing zero. -/
def leftMap : ProjectiveLine.chart K ⟶ OneGonGluing.scheme K :=
  (isPushout K).desc (OneGonGluing.torus K)
    (leftPatch K ≫ OneGonGluing.node K) (left_condition K)

/-- Normalization on the standard chart containing infinity. -/
def rightMap : ProjectiveLine.chart K ⟶ OneGonGluing.scheme K :=
  (isPushout K).desc ((ProjectiveLine.inversion K).hom ≫ OneGonGluing.torus K)
    (rightPatch K ≫ OneGonGluing.node K) (right_condition K)

@[reassoc (attr := simp)]
theorem overlapLeft_leftMap : ProjectiveLine.overlapLeft K ≫ leftMap K =
    OneGonGluing.torus K := (isPushout K).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem openOne_leftMap : openOne K ≫ leftMap K = leftPatch K ≫ OneGonGluing.node K :=
  (isPushout K).inr_desc _ _ _

@[reassoc (attr := simp)]
theorem overlapLeft_rightMap : ProjectiveLine.overlapLeft K ≫ rightMap K =
    (ProjectiveLine.inversion K).hom ≫ OneGonGluing.torus K := (isPushout K).inl_desc _ _ _

@[reassoc (attr := simp)]
theorem openOne_rightMap : openOne K ≫ rightMap K = rightPatch K ≫ OneGonGluing.node K :=
  (isPushout K).inr_desc _ _ _

/-- The projective charts agree on their full Laurent overlap. -/
theorem condition : ProjectiveLine.overlapLeft K ≫ leftMap K =
    ProjectiveLine.overlapRight K ≫ rightMap K := by
  rw [overlapLeft_leftMap, ProjectiveLine.overlapRight, Category.assoc,
    overlapLeft_rightMap, ← Category.assoc]
  have hi : (ProjectiveLine.inversion K).hom ≫ (ProjectiveLine.inversion K).hom = 𝟙 _ := by
    rw [ProjectiveLine.inversion_hom, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro p
    exact LaurentPolynomial.involutive_invert p
  rw [hi, Category.id_comp]

/-- The normalization morphism from the specified projective line. -/
def normalization : ProjectiveLine.scheme K ⟶ OneGonGluing.scheme K :=
  pushout.desc (leftMap K) (rightMap K) (condition K)

@[reassoc (attr := simp)]
theorem left_normalization : ProjectiveLine.left K ≫ normalization K = leftMap K :=
  pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_normalization : ProjectiveLine.right K ≫ normalization K = rightMap K :=
  pushout.inr_desc _ _ _

/-- Evaluation at zero on D(X-1). -/
def evalZero : awayOne K →+* K :=
  IsLocalization.Away.lift (X - 1 : K[X]) (g := evalRingHom 0) (by simp)

@[simp]
theorem evalZero_algebraMap (p : K[X]) :
    evalZero K (algebraMap K[X] (awayOne K) p) = p.eval 0 :=
  IsLocalization.Away.lift_eq _ _ _

theorem evalZero_denominator_inv : evalZero K (↑(denominator K)⁻¹ : awayOne K) = -1 := by
  have h : Units.map (evalZero K) (denominator K) = (-1 : Kˣ) := by
    apply Units.ext
    simp
  have hi := congrArg (fun v : Kˣ ↦ (↑v⁻¹ : K)) h
  exact hi

@[simp]
theorem evalZero_leftCoordinate : evalZero K (leftCoordinate K) = 0 := by
  simp [leftCoordinate]

@[simp]
theorem evalZero_rightCoordinate : evalZero K (rightCoordinate K) = 1 := by
  simp [rightCoordinate]

/-- The zero point lies in the principal open used by both normalization charts. -/
def zeroLift : Spec (.of K) ⟶ Spec (.of (awayOne K)) :=
  Spec.map (CommRingCat.ofHom (evalZero K))

@[reassoc (attr := simp)]
theorem zeroLift_openOne : zeroLift K ≫ openOne K = ProjectiveLine.chartZero K := by
  rw [zeroLift, openOne, ProjectiveLine.chartZero, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (evalZero_algebraMap K)

theorem evalZero_aeval (c : awayOne K) :
    (evalZero K).comp (aeval c).toRingHom = evalRingHom (evalZero K c) := by
  apply Polynomial.ringHom_ext
  · intro r
    change evalZero K (aeval c (C r)) = eval (evalZero K c) (C r)
    rw [aeval_C, eval_C]
    rw [IsScalarTower.algebraMap_apply K K[X] (awayOne K)]
    exact (evalZero_algebraMap K (C r)).trans (eval_C)
  · change evalZero K (aeval c X) = eval (evalZero K c) X
    rw [aeval_X, eval_X]

@[reassoc (attr := simp)]
theorem zeroLift_leftPatch : zeroLift K ≫ leftPatch K = bOrigin K := by
  rw [zeroLift, leftPatch, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((evalZero K).comp (aeval (leftCoordinate K)).toRingHom).comp
      (B (R := K)).val.toRingHom)) = _
  rw [evalZero_aeval, evalZero_leftCoordinate]
  rfl

@[reassoc (attr := simp)]
theorem zeroLift_rightPatch : zeroLift K ≫ rightPatch K = bOrigin K := by
  rw [zeroLift, rightPatch, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((evalZero K).comp (aeval (rightCoordinate K)).toRingHom).comp
      (B (R := K)).val.toRingHom)) = _
  rw [evalZero_aeval, evalZero_rightCoordinate]
  congr 1
  ext p
  exact p.property.symm

@[reassoc (attr := simp)]
theorem zero_normalization : ProjectiveLine.zero K ≫ normalization K =
    bOrigin K ≫ OneGonGluing.node K := by
  rw [ProjectiveLine.zero, Category.assoc, left_normalization,
    ← zeroLift_openOne, Category.assoc, openOne_leftMap, ← Category.assoc,
    zeroLift_leftPatch]

@[reassoc (attr := simp)]
theorem infinity_normalization : ProjectiveLine.infinity K ≫ normalization K =
    bOrigin K ≫ OneGonGluing.node K := by
  rw [ProjectiveLine.infinity, Category.assoc, right_normalization,
    ← zeroLift_openOne, Category.assoc, openOne_rightMap, ← Category.assoc,
    zeroLift_rightPatch]

/-- The two specified endpoints are identified by the normalization. -/
theorem endpoints : ProjectiveLine.zero K ≫ normalization K =
    ProjectiveLine.infinity K ≫ normalization K := by simp

end FLT.Mazur.OneGonNormalization
