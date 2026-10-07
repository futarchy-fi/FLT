/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityPairSection
public import FLT.Mazur.WeierstrassAdditionInfinitySections
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Scheme neighborhoods carrying regular addition at infinity

The localized domains are actual open subschemes of the input-chart products.
The new Y-chart domain contains the pair of infinity sections over the entire
base, and its addition morphism sends that section to infinity.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The domain inclusion for any polynomial projective addition output chart. -/
def projectiveAdditionInclusion (j k t : Fin 3) :
    Spec (CommRingCat.of (AdditionOutputOpen W j k t)) ⟶
      Spec (CommRingCat.of (ChartProduct W j k)) :=
  Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)

/-- Each normalized polynomial output domain is genuinely open in the input product. -/
instance projectiveAdditionInclusion_isOpenImmersion (j k t : Fin 3) :
    IsOpenImmersion (projectiveAdditionInclusion W j k t) :=
  IsOpenImmersion.of_isLocalization (chartProductAdditionCoordinates W j k t)

/-- Inclusion of the two-stage infinity addition domain into the Y-chart product. -/
def infinityAdditionInclusion : Spec (CommRingCat.of (InfinityAdditionOpen W)) ⟶
    Spec (CommRingCat.of (ChartProduct W 1 1)) :=
  Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom)

/-- The regular infinity addition domain is an open subscheme of the actual input product. -/
instance infinityAdditionInclusion_isOpenImmersion :
    IsOpenImmersion (infinityAdditionInclusion W) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom
    ((infinityOutputRestriction W).toRingHom.comp (infinitySlopeRestriction W).toRingHom)))
  rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (infinitySlopeRestriction W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityDen W (AlgHom.id R _))
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (infinityOutputRestriction W).toRingHom)) :=
    IsOpenImmersion.of_isLocalization (infinityOutputCoordinates W 1)
  infer_instance

/-- The regular addition morphism into the curve chart containing infinity. -/
def infinityAdditionSpec : Spec (CommRingCat.of (InfinityAdditionOpen W)) ⟶
    Spec (CommRingCat.of (Coordinate W 1)) :=
  Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom)

/-- The pair of infinity points lifted into this open neighborhood. -/
def infinityPairSectionSpec : Spec (CommRingCat.of R) ⟶
    Spec (CommRingCat.of (InfinityAdditionOpen W)) :=
  Spec.map (CommRingCat.ofHom (infinityPairAdditionLift W).toRingHom)

/-- The lifted scheme section is the original infinity pair in the input product. -/
theorem infinityPairSectionSpec_inclusion :
    infinityPairSectionSpec W ≫ infinityAdditionInclusion W =
      Spec.map (CommRingCat.ofHom (infinityPairEvaluation W).toRingHom) := by
  rw [infinityPairSectionSpec, infinityAdditionInclusion, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((infinityPairAdditionLift W).comp (infinityAdditionRestriction W)).toRingHom) = _
  rw [infinityPairAdditionLift_restriction]

/-- The scheme addition map sends the pair section to the actual infinity point. -/
theorem infinityPairSectionSpec_addition :
    infinityPairSectionSpec W ≫ infinityAdditionSpec W =
      Spec.map (CommRingCat.ofHom (chartInfinityEvaluation (S := R) W).toRingHom) := by
  rw [infinityPairSectionSpec, infinityAdditionSpec, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((infinityPairAdditionLift W).comp (infinityAdditionChart W)).toRingHom) = _
  rw [infinityAdditionChart_pair]

end FLT.Mazur.WeierstrassIntegralChart
