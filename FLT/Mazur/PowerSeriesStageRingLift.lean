/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesStageReconstruction

/-!
# Ring maps reconstructed from actual truncated coefficient maps

The reconstructed coefficients preserve ring operations because all original
stage evaluations do, and these evaluations jointly detect equality.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonInfinitesimalStages

variable (R : Type*) [CommRing R] {A : Type*} [CommRing A]
variable (f : ∀ m, A →+* Ring R m)
  (hf : ∀ m, (restriction R m).toRingHom.comp (f (m + 1)) = f m)

/-- Reconstruct a ring map with the prescribed, adjacent-compatible finite-order maps. -/
def seriesStageRingLift : A →+* PowerSeries R where
  toFun a := seriesOfStages R (fun m ↦ f m a) (fun m ↦ DFunLike.congr_fun (hf m) a)
  map_one' := by
    apply seriesToStage_ext R
    intro m
    rw [seriesToStage_seriesOfStages, map_one, map_one]
  map_mul' a b := by
    apply seriesToStage_ext R
    intro m
    rw [map_mul, seriesToStage_seriesOfStages, seriesToStage_seriesOfStages,
      seriesToStage_seriesOfStages, map_mul]
  map_zero' := by
    apply seriesToStage_ext R
    intro m
    rw [seriesToStage_seriesOfStages, map_zero, map_zero]
  map_add' a b := by
    apply seriesToStage_ext R
    intro m
    rw [map_add, seriesToStage_seriesOfStages, seriesToStage_seriesOfStages,
      seriesToStage_seriesOfStages, map_add]

/-- Each original stage evaluation of the reconstructed ring map is the specified ring map. -/
@[simp] theorem seriesToStage_ringLift (m : ℕ) (a : A) :
    seriesToStage R m (seriesStageRingLift R f hf a) = f m a :=
  seriesToStage_seriesOfStages R (fun k ↦ f k a)
    (fun k ↦ DFunLike.congr_fun (hf k) a) m

/-- The reconstruction equation as an equality of ring homomorphisms. -/
theorem seriesToStage_comp_ringLift (m : ℕ) :
    (seriesToStage R m).toRingHom.comp (seriesStageRingLift R f hf) = f m := by
  ext a : 1
  exact seriesToStage_ringLift R f hf m a

/-- A complete-base ring map is uniquely determined by these actual finite-order maps. -/
theorem seriesStageRingLift_unique (g : A →+* PowerSeries R)
    (hg : ∀ m, (seriesToStage R m).toRingHom.comp g = f m) :
    g = seriesStageRingLift R f hf := by
  ext a : 1
  apply seriesToStage_ext R
  intro m
  rw [seriesToStage_ringLift]
  exact DFunLike.congr_fun (hg m) a

end FLT.Mazur.PolygonInfinitesimalStages
