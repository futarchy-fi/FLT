/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonFirstUniversalNodeReduction

/-!
# Adjacent restriction of the full universal node

The exact restriction kernel is the original top parameter-power ideal.
Every map killing the original parameter descends, and the descended map
still kills that parameter, with the independent Laurent variable retained.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentPolynomial PolygonScalingNaturality LaurentCoefficientEvaluation
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R : Type) [CommRing R] (m : ℕ)
local notation "A" => Ring R (m + 1)
local notation "B" => Ring R m
local notation "t" => C (parameter R (m + 1))
local notation "s" => C (parameter R m)
local notation "ω" => C (parameter R (m + 1) ^ (m + 1))
local notation "r" => coeffMap (AlgHom.toRingHom (restriction R m))

/-- Every Laurent coefficient function lifts along adjacent original restriction. -/
theorem universalCoefficientRestriction_surjective : Function.Surjective (r) := by
  apply laurent_surjective_of_generators
  · intro b
    obtain ⟨a, rfl⟩ := restriction_surjective R m b
    exact ⟨C a, coeffMap_C _ _⟩
  · exact ⟨T 1, coeffMap_T _ _⟩
  · exact ⟨T (-1), coeffMap_T _ _⟩

/-- The full coefficient kernel is the unchanged top parameter-power ideal. -/
theorem universalCoefficientRestriction_ker :
    RingHom.ker (r) = Ideal.span {C (parameter R (m + 1) ^ (m + 1))} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · apply LaurentCoefficientDivisibility.coeffMap_kernel_dvd
    intro a ha
    obtain ⟨w, hw⟩ := (restriction_eq_zero_iff R m a).mp ha
    exact ⟨w, hw.symm⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, coeffMap_C]
    change C (restriction R m (parameter R (m + 1) ^ (m + 1))) * _ = 0
    rw [map_pow, restriction_parameter, parameter_pow, map_zero, zero_mul]

/-- Adjacent restriction on the original node with independent Laurent parameter. -/
def universalNodeRestriction : ChartRing (t) →+* ChartRing (s) :=
  ringMap (r) (t) (s) (by
    rw [coeffMap_C]
    exact congrArg C (restriction_parameter R m))

/-- Adjacent node restriction is onto every original node function. -/
theorem universalNodeRestriction_surjective :
    Function.Surjective (universalNodeRestriction R m) :=
  ringMap_surjective _ _ _ _ (universalCoefficientRestriction_surjective R m)

/-- The full node kernel is the extended top parameter-power ideal. -/
theorem universalNodeRestriction_ker :
    RingHom.ker (universalNodeRestriction R m) =
      Ideal.span {algebraMap (A)[T;T⁻¹] (ChartRing (t)) (ω)} := by
  rw [universalNodeRestriction, ringMap_ker _ _ _ _
    (universalCoefficientRestriction_surjective R m), universalCoefficientRestriction_ker,
    Ideal.map_span, Set.image_singleton]

/-- The original smoothing parameter retains its exact adjacent value. -/
theorem universalNodeRestriction_parameter :
    universalNodeRestriction R m (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (t)) =
      algebraMap (B)[T;T⁻¹] (ChartRing (s)) (s) := by
  rw [universalNodeRestriction, ringMap_scalar, coeffMap_C]
  exact congrArg (fun z ↦ algebraMap (B)[T;T⁻¹] (ChartRing (s)) (C z))
    (restriction_parameter R m)

variable {T : Type*} [CommRing T] (f : ChartRing (C (parameter R (m + 1))) →+* T)
  (hf : f (algebraMap (Ring R (m + 1))[T;T⁻¹]
    (ChartRing (C (parameter R (m + 1)))) (C (parameter R (m + 1)))) = 0)

include hf in
/-- Killing the original parameter kills the exact adjacent node restriction kernel. -/
theorem universalNodeRestriction_ker_le :
    RingHom.ker (universalNodeRestriction R m) ≤ RingHom.ker f := by
  rw [universalNodeRestriction_ker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  simp only [map_pow, hf, zero_pow (Nat.succ_ne_zero m)]

/-- The actual factor through the full preceding universal source node. -/
def universalNodeDesc : ChartRing (s) →+* T :=
  (universalNodeRestriction R m).liftOfSurjective
    (universalNodeRestriction_surjective R m)
    ⟨f, universalNodeRestriction_ker_le R m f hf⟩

/-- Adjacent descent preserves every original source function. -/
theorem universalNodeDesc_comp :
    (universalNodeDesc R m f hf).comp (universalNodeRestriction R m) = f := by
  apply RingHom.ext
  intro z
  exact (universalNodeRestriction R m).liftOfSurjective_comp_apply
    (universalNodeRestriction_surjective R m)
    ⟨f, universalNodeRestriction_ker_le R m f hf⟩ z

/-- The descended receiving map still kills the original smoothing parameter. -/
theorem universalNodeDesc_parameter :
    universalNodeDesc R m f hf (algebraMap (B)[T;T⁻¹] (ChartRing (s)) (s)) = 0 := by
  have he := RingHom.congr_fun (universalNodeDesc_comp R m f hf)
    (algebraMap (A)[T;T⁻¹] (ChartRing (t)) (t))
  change universalNodeDesc R m f hf (universalNodeRestriction R m _) = _ at he
  rw [universalNodeRestriction_parameter, hf] at he
  exact he

end FLT.Mazur.PolygonInfinitesimalStages
