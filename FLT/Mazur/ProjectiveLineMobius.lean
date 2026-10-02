/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.OneGonNormalization

/-! # The projective coordinate change t ↦ t/(t-1) -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open scoped LaurentPolynomial
open FLT.Mazur.OneGonTransition FLT.Mazur.OneGonNormalization
open FLT.Mazur.OneGonRefinedDescent

namespace FLT.Mazur.ProjectiveLineMobius

universe u
variable (K : Type u) [Field K]

theorem inversion_square :
    (ProjectiveLine.inversion K).hom ≫ (ProjectiveLine.inversion K).hom = 𝟙 _ := by
  rw [ProjectiveLine.inversion_hom, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply ConcreteCategory.hom_ext
  intro p
  change LaurentPolynomial.invert (LaurentPolynomial.invert p) = p
  exact LaurentPolynomial.involutive_invert p

@[reassoc]
theorem inversion_overlapRight :
    (ProjectiveLine.inversion K).hom ≫ ProjectiveLine.overlapRight K =
      ProjectiveLine.overlapLeft K := by
  rw [ProjectiveLine.overlapRight, ← Category.assoc, inversion_square, Category.id_comp]

@[reassoc]
theorem inversion_torusToRight :
    (ProjectiveLine.inversion K).hom ≫ torusToRight K =
      ProjectiveLine.overlapLeft K ≫ (reflection K).hom := by
  rw [torusToRight, inversion_overlapRight_assoc]

/-- The common Laurent coordinate 1-t/(t-1) on the puncture. -/
def reflectedOverlap : Spec (.of (puncture K)) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom
    (LaurentUnitPoints.evalUnit (R := K) (-(difference K)⁻¹)).toRingHom)

@[reassoc]
theorem reflectedOverlap_left :
    reflectedOverlap K ≫ ProjectiveLine.overlapLeft K =
      toTorus K ≫ ProjectiveLine.overlapLeft K ≫ (reflection K).hom := by
  have h :
      (LaurentUnitPoints.evalUnit (R := K) (-(difference K)⁻¹)).toRingHom.comp toLaurent =
      (overlapMap K).comp (toLaurent.comp (reflectionEquiv K).toRingHom) := by
    ext r
    · simp
    · change LaurentUnitPoints.evalUnit (R := K) (-(difference K)⁻¹) (toLaurent (X : K[X])) =
        overlapMap K (toLaurent ((X : K[X]).comp (1 - X)))
      simp only [toLaurent_X, LaurentUnitPoints.evalUnit_T, zpow_one, Units.val_neg,
        X_comp, map_sub, map_one, overlapMap_T]
      have h := mobius_sub_one K
      linear_combination h
  simpa only [reflectedOverlap, ProjectiveLine.overlapLeft, toTorus_eq_specMap,
    reflection_hom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    using congrArg (fun φ : K[X] →+* puncture K ↦ Spec.map (CommRingCat.ofHom φ)) h

@[reassoc]
theorem reflectedOverlap_right :
    reflectedOverlap K ≫ ProjectiveLine.overlapRight K =
      toOverlap K ≫ ProjectiveLine.overlapLeft K ≫ (reflection K).hom := by
  have h :
      (LaurentUnitPoints.evalUnit (R := K) (-(difference K)⁻¹)).toRingHom.comp
        (LaurentPolynomial.invert.toRingHom.comp toLaurent) =
      (torusRestriction K).comp (toLaurent.comp (reflectionEquiv K).toRingHom) := by
    ext r
    · simp
    · change LaurentUnitPoints.evalUnit (R := K) (-(difference K)⁻¹)
          (LaurentPolynomial.invert (toLaurent (X : K[X]))) =
        torusRestriction K (toLaurent ((X : K[X]).comp (1 - X)))
      simp [difference_val]
  simpa only [reflectedOverlap, ProjectiveLine.overlapRight, ProjectiveLine.inversion_hom,
    ProjectiveLine.overlapLeft, toOverlap_eq, reflection_hom,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    using congrArg (fun φ : K[X] →+* puncture K ↦ Spec.map (CommRingCat.ofHom φ)) h

theorem exists_affineMap :
    ∃ f : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K,
      ProjectiveLine.overlapRight K ≫ f =
        ProjectiveLine.overlapLeft K ≫ (reflection K).hom ≫ ProjectiveLine.right K ∧
      torusToRight K ≫ f =
        ProjectiveLine.overlapLeft K ≫ (reflection K).hom ≫ ProjectiveLine.left K := by
  apply exists_glue_two (ProjectiveLine.overlapRight K) (torusToRight K) (right_cover K)
  apply (cancel_epi (overlap_isPullback K).flip.isoPullback.hom).mp
  simp only [← Category.assoc, IsPullback.isoPullback_hom_fst,
    IsPullback.isoPullback_hom_snd]
  rw [Category.assoc (toOverlap K), ← reflectedOverlap_right,
    Category.assoc (toTorus K), ← reflectedOverlap_left]
  exact congrArg (fun m ↦ reflectedOverlap K ≫ m) (ProjectiveLine.overlap_condition K).symm

/-- The fractional linear map on the affine chart, including its pole. -/
def affineMap : ProjectiveLine.chart K ⟶ ProjectiveLine.scheme K :=
  (exists_affineMap K).choose

@[reassoc (attr := simp)]
theorem overlap_affineMap : ProjectiveLine.overlapRight K ≫ affineMap K =
    ProjectiveLine.overlapLeft K ≫ (reflection K).hom ≫ ProjectiveLine.right K :=
  (exists_affineMap K).choose_spec.1

@[reassoc (attr := simp)]
theorem torus_affineMap : torusToRight K ≫ affineMap K =
    ProjectiveLine.overlapLeft K ≫ (reflection K).hom ≫ ProjectiveLine.left K :=
  (exists_affineMap K).choose_spec.2

theorem affine_compatible :
    ProjectiveLine.overlapLeft K ≫ affineMap K =
      ProjectiveLine.overlapRight K ≫ (reflection K).hom ≫ ProjectiveLine.right K := by
  rw [← inversion_overlapRight K, Category.assoc, overlap_affineMap]
  rfl

/-- The global fractional linear transformation t ↦ t/(t-1). -/
def map : ProjectiveLine.scheme K ⟶ ProjectiveLine.scheme K :=
  pushout.desc (affineMap K) ((reflection K).hom ≫ ProjectiveLine.right K)
    (affine_compatible K)

@[reassoc (attr := simp)]
theorem left_map : ProjectiveLine.left K ≫ map K = affineMap K := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_map : ProjectiveLine.right K ≫ map K =
    (reflection K).hom ≫ ProjectiveLine.right K := pushout.inr_desc _ _ _

/-- The coordinate change is an involution, proved on the refined affine cover. -/
theorem map_square : map K ≫ map K = 𝟙 _ := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    simp only [left_map_assoc, Category.comp_id]
    apply hom_ext_two (ProjectiveLine.overlapRight K) (torusToRight K) (right_cover K)
    · simp only [overlap_affineMap_assoc, right_map]
      rw [← Category.assoc (reflection K).hom, reflection_square, Category.id_comp]
      apply (cancel_epi (ProjectiveLine.inversion K).hom).mp
      simp only [← Category.assoc, inversion_overlapRight]
      exact (ProjectiveLine.overlap_condition K).symm
    · rw [torus_affineMap_assoc, ← inversion_torusToRight_assoc, left_map]
      rw [torus_affineMap, ← inversion_torusToRight_assoc,
        ← Category.assoc, inversion_square, Category.id_comp]
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    simp only [right_map_assoc, right_map, Category.comp_id]
    rw [← Category.assoc, reflection_square, Category.id_comp]

/-- The change from the (0,1) marking to the (0,∞) marking. -/
def iso : ProjectiveLine.scheme K ≅ ProjectiveLine.scheme K where
  hom := map K
  inv := map K
  hom_inv_id := map_square K
  inv_hom_id := map_square K


open OneGonLocalFactorization

/-- The torus point with coordinate one. -/
def unitOne : Spec (.of K) ⟶ ProjectiveLine.overlap K :=
  Spec.map (CommRingCat.ofHom (LaurentUnitPoints.evalUnit (R := K) (1 : Kˣ)).toRingHom)

@[reassoc]
theorem unitOne_left : unitOne K ≫ ProjectiveLine.overlapLeft K = endpointSection (1 : K) := by
  rw [unitOne, ProjectiveLine.overlapLeft, endpointSection, ← Spec.map_comp]
  congr 1
  ext r <;> simp

@[reassoc]
theorem unitOne_right : unitOne K ≫ ProjectiveLine.overlapRight K = endpointSection (1 : K) := by
  rw [unitOne, ProjectiveLine.overlapRight, ProjectiveLine.inversion_hom,
    ProjectiveLine.overlapLeft, ← Spec.map_comp, ← Spec.map_comp, endpointSection]
  congr 1
  ext r <;> simp

@[reassoc]
theorem endpoint_reflection (a : K) :
    endpointSection a ≫ (reflection K).hom = endpointSection (1 - a) := by
  rw [endpointSection, reflection_hom, endpointSection, ← Spec.map_comp]
  congr 1
  ext r <;> simp

theorem one_left_eq_right :
    endpointSection (1 : K) ≫ ProjectiveLine.left K =
      endpointSection (1 : K) ≫ ProjectiveLine.right K := by
  have h := congrArg (fun m ↦ unitOne K ≫ m) (ProjectiveLine.overlap_condition K)
  simpa only [unitOne_left_assoc, unitOne_right_assoc] using h

@[reassoc]
theorem unitOne_torusToRight :
    unitOne K ≫ torusToRight K = endpointSection (0 : K) := by
  rw [torusToRight, unitOne_right_assoc, endpoint_reflection, sub_self]

@[reassoc (attr := simp)]
theorem zero_map : ProjectiveLine.zero K ≫ map K = ProjectiveLine.zero K := by
  change endpointSection (0 : K) ≫ ProjectiveLine.left K ≫ map K =
    endpointSection (0 : K) ≫ ProjectiveLine.left K
  rw [left_map, ← unitOne_torusToRight K, Category.assoc, torus_affineMap,
    unitOne_left_assoc, endpoint_reflection_assoc, sub_self, unitOne_torusToRight]

@[reassoc (attr := simp)]
theorem infinity_map :
    ProjectiveLine.infinity K ≫ map K =
      endpointSection (1 : K) ≫ ProjectiveLine.left K := by
  change endpointSection (0 : K) ≫ ProjectiveLine.right K ≫ map K = _
  rw [right_map, endpoint_reflection_assoc, sub_zero, ← one_left_eq_right]

@[reassoc]
theorem one_map :
    endpointSection (1 : K) ≫ ProjectiveLine.left K ≫ map K = ProjectiveLine.infinity K := by
  rw [← Category.assoc, one_left_eq_right, Category.assoc, right_map,
    endpoint_reflection_assoc, sub_self]
  rfl

@[reassoc]
theorem reflection_toBase :
    (reflection K).hom ≫ ProjectiveLine.chartToBase K = ProjectiveLine.chartToBase K := by
  rw [reflection_hom, ProjectiveLine.chartToBase, ← Spec.map_comp]
  congr 1
  ext r
  simp

@[reassoc]
theorem map_toBase :
    map K ≫ ProjectiveLine.toBase K = ProjectiveLine.toBase K := by
  apply pushout.hom_ext
  · change ProjectiveLine.left K ≫ _ = ProjectiveLine.left K ≫ _
    rw [left_map_assoc, ProjectiveLine.left_toBase]
    apply hom_ext_two (ProjectiveLine.overlapRight K) (torusToRight K) (right_cover K)
    · rw [overlap_affineMap_assoc, ProjectiveLine.right_toBase, reflection_toBase]
      exact ProjectiveLine.overlap_toBase K
    · rw [torus_affineMap_assoc, ProjectiveLine.left_toBase, reflection_toBase]
      rw [torusToRight, Category.assoc, reflection_toBase]
      exact ProjectiveLine.overlap_toBase K
  · change ProjectiveLine.right K ≫ _ = ProjectiveLine.right K ≫ _
    rw [right_map_assoc, ProjectiveLine.right_toBase, reflection_toBase]

end FLT.Mazur.ProjectiveLineMobius
