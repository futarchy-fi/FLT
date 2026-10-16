/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap
public import FLT.Mazur.PolygonStageCoefficientKernel
public import FLT.Mazur.LaurentCoefficientDivisibility
public import FLT.Mazur.LaurentRingSurjectivity

/-!
# The full original universal node descends to order zero

The first-stage chart restriction is surjective and has exactly the original
smoothing-parameter ideal as kernel. Any map killing that parameter therefore
factors through the entire order-zero chart, with its Laurent variable retained.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R]
local notation "A" => Ring R 1
local notation "B" => Ring R 0
local notation "t" => C (parameter R 1)
local notation "s" => C (parameter R 0)
local notation "r" => coeffMap (AlgHom.toRingHom (restriction R 0))

/-- The original Laurent coefficient restriction is onto. -/
theorem firstUniversalCoefficientRestriction_surjective : Function.Surjective (r) := by
  apply laurent_surjective_of_generators
  · intro b
    obtain ⟨a, rfl⟩ := restriction_surjective R 0 b
    exact ⟨C a, coeffMap_C _ _⟩
  · exact ⟨T 1, coeffMap_T _ _⟩
  · exact ⟨T (-1), coeffMap_T _ _⟩

/-- Its entire kernel is the original smoothing parameter, including both Laurent directions. -/
theorem firstUniversalCoefficientRestriction_ker : RingHom.ker (r) = Ideal.span {(t)} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · apply LaurentCoefficientDivisibility.coeffMap_kernel_dvd
    intro a ha
    obtain ⟨w, hw⟩ := (restriction_eq_zero_iff R 0 a).mp ha
    exact ⟨w, by simpa only [zero_add, pow_one] using hw.symm⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, coeffMap_C]
    change C (restriction R 0 (parameter R 1)) * _ = 0
    rw [restriction_parameter]
    have hz : parameter R 0 = 0 := by simpa only [zero_add, pow_one] using parameter_pow R 0
    rw [hz, map_zero, zero_mul]

/-- The actual original node chart restriction with the independent parameter unchanged. -/
def firstUniversalNodeRestriction : ChartRing (t) →+* ChartRing (s) :=
  ringMap (r) (t) (s) (by
    rw [coeffMap_C]
    exact congrArg C (restriction_parameter R 0))

/-- All functions on the full order-zero universal chart lift to the original first chart. -/
theorem firstUniversalNodeRestriction_surjective :
    Function.Surjective (firstUniversalNodeRestriction R) :=
  ringMap_surjective _ _ _ _ (firstUniversalCoefficientRestriction_surjective R)

/-- The full chart kernel is exactly its original parameter ideal. -/
theorem firstUniversalNodeRestriction_ker :
    RingHom.ker (firstUniversalNodeRestriction R) =
      Ideal.span {algebraMap (A)[T;T⁻¹] (ChartRing (t)) (t)} := by
  rw [firstUniversalNodeRestriction, ringMap_ker _ _ _ _
    (firstUniversalCoefficientRestriction_surjective R), firstUniversalCoefficientRestriction_ker,
    Ideal.map_span, Set.image_singleton]

variable {T : Type*} [CommRing T] (f : ChartRing (C (parameter R 1)) →+* T)
  (hf : f (algebraMap (Ring R 1)[T;T⁻¹]
    (ChartRing (C (parameter R 1))) (C (parameter R 1))) = 0)

include hf in
/-- Killing the parameter kills the exact chart restriction kernel. -/
theorem firstUniversalNodeRestriction_ker_le :
    RingHom.ker (firstUniversalNodeRestriction R) ≤ RingHom.ker f := by
  rw [firstUniversalNodeRestriction_ker, Ideal.span_le, Set.singleton_subset_iff]
  exact hf

/-- The constructed factor through the full original order-zero source chart. -/
def firstUniversalNodeDesc : ChartRing (s) →+* T :=
  (firstUniversalNodeRestriction R).liftOfSurjective
    (firstUniversalNodeRestriction_surjective R)
    ⟨f, firstUniversalNodeRestriction_ker_le R f hf⟩

/-- The factor retains every original source function. -/
theorem firstUniversalNodeDesc_comp :
    (firstUniversalNodeDesc R f hf).comp (firstUniversalNodeRestriction R) = f := by
  apply RingHom.ext
  intro z
  exact (firstUniversalNodeRestriction R).liftOfSurjective_comp_apply
    (firstUniversalNodeRestriction_surjective R)
    ⟨f, firstUniversalNodeRestriction_ker_le R f hf⟩ z

end FLT.Mazur.PolygonInfinitesimalStages
