/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PowerSeriesStageRingLift
public import FLT.Mazur.PolygonPowerSeriesSystem

/-!
# Reconstructing compatible points in an affine scheme

Full faithfulness of Spec turns the actual adjacent scheme equations into
compatible ring maps. Their reconstruction gives a point over the complete base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (A : CommRingCat)
variable (s : ∀ m, Spec (.of (Ring R m)) ⟶ Spec A)
  (hs : ∀ m, baseRestriction R m ≫ s (m + 1) = s m)

include hs in
/-- The actual affine coordinate maps retain adjacent compatibility. -/
theorem affineStageCoordinates_compatible (m : ℕ) :
    (restriction R m).toRingHom.comp (Spec.preimage (s (m + 1))).hom =
      (Spec.preimage (s m)).hom := by
  have he := congrArg Spec.preimage (hs m)
  rw [Spec.preimage_comp, baseRestriction, Spec.preimage_map] at he
  exact congrArg CommRingCat.Hom.hom he

/-- The complete point reconstructed from the original affine stage maps. -/
def affineStagePoint : Spec (.of (PowerSeries R)) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (seriesStageRingLift R
    (fun m ↦ (Spec.preimage (s m)).hom) (affineStageCoordinates_compatible R A s hs)))

/-- Restricting the complete affine point recovers every original finite-order point. -/
@[reassoc] theorem baseToSeries_affineStagePoint (m : ℕ) :
    baseToSeries R m ≫ affineStagePoint R A s hs = s m := by
  rw [baseToSeries, affineStagePoint, ← Spec.map_comp]
  have he := seriesToStage_comp_ringLift R
    (fun m ↦ (Spec.preimage (s m)).hom) (affineStageCoordinates_compatible R A s hs) m
  have hc : CommRingCat.ofHom (seriesStageRingLift R
      (fun m ↦ (Spec.preimage (s m)).hom) (affineStageCoordinates_compatible R A s hs)) ≫
      CommRingCat.ofHom (seriesToStage R m).toRingHom = Spec.preimage (s m) :=
    CommRingCat.hom_ext he
  rw [hc, Spec.map_preimage]

/-- Maps from the complete coefficient spectrum to an affine spectrum are detected at all stages. -/
theorem affinePoint_ext {f g : Spec (.of (PowerSeries R)) ⟶ Spec A}
    (he : ∀ m, baseToSeries R m ≫ f = baseToSeries R m ≫ g) : f = g := by
  apply Spec.preimage_injective
  apply CommRingCat.hom_ext
  ext a : 1
  apply seriesToStage_ext R
  intro m
  have hm := congrArg Spec.preimage (he m)
  simp only [Spec.preimage_comp, baseToSeries, Spec.preimage_map] at hm
  exact ConcreteCategory.congr_hom hm a

/-- The reconstructed affine point is the unique point with these finite restrictions. -/
theorem affineStagePoint_unique (f : Spec (.of (PowerSeries R)) ⟶ Spec A)
    (hf : ∀ m, baseToSeries R m ≫ f = s m) : f = affineStagePoint R A s hs := by
  apply affinePoint_ext R A
  intro m
  rw [hf, baseToSeries_affineStagePoint]

end FLT.Mazur.PolygonInfinitesimalStages
