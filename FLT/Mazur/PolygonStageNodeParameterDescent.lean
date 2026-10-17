/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingRingMap
public import FLT.Mazur.PolygonStageCoefficientKernel

/-!
# Parameter-zero receiving maps descend through the original node stages

The full adjacent node kernel is the last parameter power. Descent retains
both original coordinates and all other nilpotents in the receiving ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing
variable (R : Type) [CommRing R] (m : ℕ)
local notation "A" => Ring R (m + 1)
local notation "B" => Ring R m
local notation "t" => parameter R (m + 1)
local notation "s" => parameter R m
local notation "r" => AlgHom.toRingHom (restriction R m)

/-- Adjacent restriction on the full original node. -/
def stageNodeRestriction : ChartRing (t) →+* ChartRing (s) :=
  ringMap (r) (t) (s) (restriction_parameter R m)

/-- Every original lower-stage function has a lift. -/
theorem stageNodeRestriction_surjective : Function.Surjective (stageNodeRestriction R m) :=
  ringMap_surjective _ _ _ _ (restriction_surjective R m)

/-- The full node kernel is exactly the extended last parameter power. -/
theorem stageNodeRestriction_ker :
    RingHom.ker (stageNodeRestriction R m) =
      Ideal.span {algebraMap (A) (ChartRing (t)) ((t) ^ (m + 1))} := by
  have hr : RingHom.ker (r) = Ideal.span {(t) ^ (m + 1)} := by
    ext z
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    change restriction R m z = 0 ↔ (t) ^ (m + 1) ∣ z
    rw [restriction_eq_zero_iff]
    constructor <;> rintro ⟨w, hw⟩ <;> exact ⟨w, hw.symm⟩
  rw [stageNodeRestriction, ringMap_ker _ _ _ _ (restriction_surjective R m),
    hr, Ideal.map_span, Set.image_singleton]

/-- The original parameter retains its adjacent value. -/
theorem stageNodeRestriction_parameter :
    stageNodeRestriction R m (algebraMap (A) (ChartRing (t)) (t)) =
      algebraMap (B) (ChartRing (s)) (s) := by
  rw [stageNodeRestriction, ringMap_scalar]
  exact congrArg (algebraMap (B) (ChartRing (s))) (restriction_parameter R m)

/-- Restriction retains the outgoing coordinate. -/
theorem stageNodeRestriction_left :
    stageNodeRestriction R m (leftCoordinate (t)) = leftCoordinate (s) :=
  ringMap_left _ _ _ _

/-- Restriction retains the incoming coordinate. -/
theorem stageNodeRestriction_right :
    stageNodeRestriction R m (rightCoordinate (t)) = rightCoordinate (s) :=
  ringMap_right _ _ _ _

variable {D : Type} [CommRing D] (f : ChartRing (parameter R (m + 1)) →+* D)
  (hf : f (algebraMap (Ring R (m + 1))
    (ChartRing (parameter R (m + 1))) (parameter R (m + 1))) = 0)

include hf in
/-- A parameter-zero map kills the entire adjacent kernel. -/
theorem stageNodeRestriction_ker_le :
    RingHom.ker (stageNodeRestriction R m) ≤ RingHom.ker f := by
  rw [stageNodeRestriction_ker, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
  simp only [map_pow, hf, zero_pow (Nat.succ_ne_zero m)]

/-- The full receiving map on the preceding node, without reducing its target. -/
def stageNodeDesc : ChartRing (s) →+* D :=
  (stageNodeRestriction R m).liftOfSurjective (stageNodeRestriction_surjective R m)
    ⟨f, stageNodeRestriction_ker_le R m f hf⟩

/-- Descent preserves every original function. -/
theorem stageNodeDesc_comp :
    (stageNodeDesc R m f hf).comp (stageNodeRestriction R m) = f := by
  apply RingHom.ext
  intro z
  exact (stageNodeRestriction R m).liftOfSurjective_comp_apply
    (stageNodeRestriction_surjective R m) ⟨f, stageNodeRestriction_ker_le R m f hf⟩ z

/-- The descended map still kills the original parameter. -/
theorem stageNodeDesc_parameter :
    stageNodeDesc R m f hf (algebraMap (B) (ChartRing (s)) (s)) = 0 := by
  have he := RingHom.congr_fun (stageNodeDesc_comp R m f hf)
    (algebraMap (A) (ChartRing (t)) (t))
  change stageNodeDesc R m f hf (stageNodeRestriction R m _) = _ at he
  rw [stageNodeRestriction_parameter, hf] at he
  exact he

/-- Descent preserves the outgoing value in the entire receiving ring. -/
theorem stageNodeDesc_left :
    stageNodeDesc R m f hf (leftCoordinate (s)) = f (leftCoordinate (t)) := by
  have he := RingHom.congr_fun (stageNodeDesc_comp R m f hf) (leftCoordinate (t))
  change stageNodeDesc R m f hf (stageNodeRestriction R m _) = _ at he
  rwa [stageNodeRestriction_left] at he

/-- Descent preserves the incoming value in the entire receiving ring. -/
theorem stageNodeDesc_right :
    stageNodeDesc R m f hf (rightCoordinate (s)) = f (rightCoordinate (t)) := by
  have he := RingHom.congr_fun (stageNodeDesc_comp R m f hf) (rightCoordinate (t))
  change stageNodeDesc R m f hf (stageNodeRestriction R m _) = _ at he
  rwa [stageNodeRestriction_right] at he

end FLT.Mazur.PolygonInfinitesimalStages
