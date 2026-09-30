/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonChartScaling
public import FLT.Mazur.ProjectiveLineEndpoints

/-!
# Endpoint-preserving scalar multiplication on the projective line

The two affine charts scale by reciprocal units. Their Laurent restrictions
agree, giving an automorphism fixing zero and infinity over the base field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ProjectiveLine

variable (K : Type u) [Field K]

/-- Scaling on an affine chart. -/
def chartScaling (a : Kˣ) : chart K ⟶ chart K :=
  Spec.map (CommRingCat.ofHom (PolygonChartScaling.affine a))

/-- Scaling on the punctured affine chart. -/
def overlapScaling (a : Kˣ) : overlap K ⟶ overlap K :=
  Spec.map (CommRingCat.ofHom (PolygonChartScaling.laurent a))

theorem overlapLeft_chartScaling (a : Kˣ) :
    overlapLeft K ≫ chartScaling K a = overlapScaling K a ≫ overlapLeft K := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, overlapLeft, chartScaling,
    overlapScaling] using congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
      (PolygonChartScaling.toLaurent_affine a)

theorem overlapRight_chartScaling (a : Kˣ) :
    overlapRight K ≫ chartScaling K a⁻¹ = overlapScaling K a ≫ overlapRight K := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, overlapRight, inversion_hom,
    overlapLeft, chartScaling, overlapScaling, Category.assoc] using
      congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f))
        (PolygonChartScaling.invert_toLaurent_affine a)

/-- Scalar multiplication obtained by gluing the two affine formulas. -/
def scaling (a : Kˣ) : scheme K ⟶ scheme K :=
  pushout.desc (chartScaling K a ≫ left K) (chartScaling K a⁻¹ ≫ right K) (by
    rw [← Category.assoc, overlapLeft_chartScaling, Category.assoc,
      overlap_condition, ← Category.assoc, ← overlapRight_chartScaling, Category.assoc])

@[reassoc (attr := simp)]
theorem left_scaling (a : Kˣ) :
    left K ≫ scaling K a = chartScaling K a ≫ left K := pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
theorem right_scaling (a : Kˣ) :
    right K ≫ scaling K a = chartScaling K a⁻¹ ≫ right K := pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
theorem chartScaling_toBase (a : Kˣ) : chartScaling K a ≫ chartToBase K = chartToBase K := by
  have h : (PolygonChartScaling.affine a).comp Polynomial.C = Polynomial.C := by ext; simp
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, chartScaling, chartToBase] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) h

@[reassoc (attr := simp)]
theorem scaling_toBase (a : Kˣ) : scaling K a ≫ toBase K = toBase K := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    simp
  · change right K ≫ _ = right K ≫ _
    simp

@[simp]
theorem chartScaling_one : chartScaling K 1 = 𝟙 _ := by
  simp [chartScaling, PolygonChartScaling.affine_one, ← Spec.map_id]

theorem chartScaling_mul (a b : Kˣ) :
    chartScaling K (a * b) = chartScaling K a ≫ chartScaling K b := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, chartScaling] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (PolygonChartScaling.affine_mul a b)

@[simp]
theorem scaling_one : scaling K 1 = 𝟙 _ := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    simp
  · change right K ≫ _ = right K ≫ _
    simp

theorem scaling_mul (a b : Kˣ) : scaling K (a * b) = scaling K a ≫ scaling K b := by
  apply pushout.hom_ext
  · change left K ≫ _ = left K ≫ _
    simp [chartScaling_mul, Category.assoc]
  · change right K ≫ _ = right K ≫ _
    simp [chartScaling_mul, Category.assoc, mul_comm]

@[reassoc (attr := simp)]
theorem chartZero_chartScaling (a : Kˣ) : chartZero K ≫ chartScaling K a = chartZero K := by
  simpa only [CommRingCat.ofHom_comp, Spec.map_comp, chartScaling, chartZero] using
    congrArg (fun f ↦ Spec.map (CommRingCat.ofHom f)) (PolygonChartScaling.affine_zero a)

@[reassoc (attr := simp)]
theorem zero_scaling (a : Kˣ) : zero K ≫ scaling K a = zero K := by simp [zero]

@[reassoc (attr := simp)]
theorem infinity_scaling (a : Kˣ) : infinity K ≫ scaling K a = infinity K := by
  simp [infinity]

/-- The scaling endomorphism regarded over the specified base. -/
def scalingOver (a : Kˣ) : Over.mk (toBase K) ⟶ Over.mk (toBase K) :=
  Over.homMk (scaling K a) (scaling_toBase K a)

@[reassoc (attr := simp)]
theorem zeroSection_scalingOver (a : Kˣ) : zeroSection K ≫ scalingOver K a = zeroSection K := by
  apply Over.OverMorphism.ext
  exact zero_scaling K a

@[reassoc (attr := simp)]
theorem infinitySection_scalingOver (a : Kˣ) :
    infinitySection K ≫ scalingOver K a = infinitySection K := by
  apply Over.OverMorphism.ext
  exact infinity_scaling K a

@[simp]
theorem scalingOver_one : scalingOver K 1 = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact scaling_one K

theorem scalingOver_mul (a b : Kˣ) :
    scalingOver K (a * b) = scalingOver K a ≫ scalingOver K b := by
  apply Over.OverMorphism.ext
  exact scaling_mul K a b

/-- Scaling by the inverse unit is the inverse automorphism over the base. -/
def scalingOverIso (a : Kˣ) : Over.mk (toBase K) ≅ Over.mk (toBase K) where
  hom := scalingOver K a
  inv := scalingOver K a⁻¹
  hom_inv_id := by rw [← scalingOver_mul, mul_inv_cancel, scalingOver_one]
  inv_hom_id := by rw [← scalingOver_mul, inv_mul_cancel, scalingOver_one]

end FLT.Mazur.ProjectiveLine
