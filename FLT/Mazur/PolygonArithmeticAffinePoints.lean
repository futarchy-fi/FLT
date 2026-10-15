/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticStageRingLift
public import FLT.Mazur.PolygonArithmeticCompleteBaseSquare
public import FLT.Mazur.PolygonArithmeticSystem

/-!
# Reconstructing compatible points in an affine scheme

Full faithfulness of Spec turns the actual adjacent scheme equations into
compatible ring maps. Their reconstruction gives a point over the complete base.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R] (π : R) (A : CommRingCat)
variable (s : ∀ m, Spec (.of (Quotient R π m)) ⟶ Spec A)
  (hs : ∀ m, baseRestriction R π m ≫ s (m + 1) = s m)

include hs in
/-- The actual affine coordinate maps retain adjacent compatibility. -/
theorem affineStageCoordinates_compatible (m : ℕ) :
    (restriction R π m).toRingHom.comp (Spec.preimage (s (m + 1))).hom =
      (Spec.preimage (s m)).hom := by
  have he := congrArg Spec.preimage (hs m)
  rw [Spec.preimage_comp, baseRestriction, Spec.preimage_map] at he
  exact congrArg CommRingCat.Hom.hom he

variable [IsAdicComplete (ideal R π) R]

/-- The complete point reconstructed from the original affine stage maps. -/
def affineStagePoint : Spec (.of R) ⟶ Spec A :=
  Spec.map (CommRingCat.ofHom (arithmeticStageRingLift R π
    (fun m ↦ (Spec.preimage (s m)).hom) (affineStageCoordinates_compatible R π A s hs)))

/-- Restricting the complete affine point recovers every original finite-order point. -/
@[reassoc] theorem baseToIntegral_affineStagePoint (m : ℕ) :
    baseToIntegral R π m ≫ affineStagePoint R π A s hs = s m := by
  rw [baseToIntegral, affineStagePoint, ← Spec.map_comp]
  have he : (Ideal.Quotient.mk (ideal R π ^ (m + 1))).comp
      (arithmeticStageRingLift R π (fun m ↦ (Spec.preimage (s m)).hom)
        (affineStageCoordinates_compatible R π A s hs)) = (Spec.preimage (s m)).hom := by
    ext x : 1
    exact quotient_arithmeticStageRingLift R π _ _ m x
  have hc : CommRingCat.ofHom (arithmeticStageRingLift R π
      (fun m ↦ (Spec.preimage (s m)).hom) (affineStageCoordinates_compatible R π A s hs)) ≫
      CommRingCat.ofHom (Ideal.Quotient.mk (ideal R π ^ (m + 1))) = Spec.preimage (s m) :=
    CommRingCat.hom_ext he
  rw [hc, Spec.map_preimage]

/-- Maps from the complete coefficient spectrum to an affine spectrum are detected at all stages. -/
theorem affinePoint_ext {f g : Spec (.of R) ⟶ Spec A}
    (he : ∀ m, baseToIntegral R π m ≫ f = baseToIntegral R π m ≫ g) : f = g := by
  apply Spec.preimage_injective
  apply CommRingCat.hom_ext
  ext a : 1
  apply arithmeticQuotient_ext R π
  intro m
  have hm := congrArg Spec.preimage (he m)
  simp only [Spec.preimage_comp, baseToIntegral, Spec.preimage_map] at hm
  exact ConcreteCategory.congr_hom hm a

/-- The reconstructed affine point is the unique point with these finite restrictions. -/
theorem affineStagePoint_unique (f : Spec (.of R) ⟶ Spec A)
    (hf : ∀ m, baseToIntegral R π m ≫ f = s m) : f = affineStagePoint R π A s hs := by
  apply affinePoint_ext R π A
  intro m
  rw [hf, baseToIntegral_affineStagePoint]

end FLT.Mazur.PolygonArithmeticStages
