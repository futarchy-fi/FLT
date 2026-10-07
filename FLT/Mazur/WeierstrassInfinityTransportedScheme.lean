/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityTransportedComparison
public import FLT.Mazur.WeierstrassTransportedPolynomialScheme

/-!
# Infinity compatibility on the existing transported scheme cover

The output-overlap factorization is transported from the full tensor-ring
intersection to the actual fiber product of each existing affine cover member
and the infinity domain. Its projections recover the existing scheme maps.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

variable {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of (TransportedAdditionRing W 1 1 i)))
  (g : X ⟶ Spec (CommRingCat.of (InfinityAdditionOpen W)))
  (h : f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionInput W 1 1 i).toRingHom) =
    g ≫ Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom))

/-- Any common scheme over the two full domains maps to the concrete output overlap. -/
def infinityTransportedCommonOutput :
    X ⟶ Spec (CommRingCat.of (Overlap W (additionChartOutput i) 1)) :=
  (infinityTransported_isPullback W i).lift f g h ≫
    Spec.map (CommRingCat.ofHom (infinityTransportedOutputLift W i).toRingHom)

/-- The first projection of the common output recovers transported affine addition. -/
theorem infinityTransportedCommonOutput_affine :
    infinityTransportedCommonOutput W i f g h ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W (additionChartOutput i) 1).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionAffine W 1 1 i).toRingHom) ≫
        additionChartSpec W i := by
  rw [infinityTransportedCommonOutput, Category.assoc,
    infinityTransportedOutputLift_spec_affine, ← Category.assoc, IsPullback.lift_fst]

/-- The second projection recovers the existing infinity addition map. -/
theorem infinityTransportedCommonOutput_infinity :
    infinityTransportedCommonOutput W i f g h ≫
        Spec.map (CommRingCat.ofHom (transitionBase W (additionChartOutput i) 1).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) := by
  rw [infinityTransportedCommonOutput, Category.assoc,
    infinityTransportedOutputLift_spec_infinity, ← Category.assoc, IsPullback.lift_snd]

variable (hΔ : IsUnit W.Δ)

/-- The full intersection of an existing transported cover member with the infinity domain. -/
abbrev InfinityTransportedScheme := pullback (transportedPolynomialDomainMap W 1 1 i hΔ)
  (Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom))

/-- The ring identification preserves the common original Y-chart input map. -/
theorem infinityTransportedScheme_inputs :
    (pullback.fst (transportedPolynomialDomainMap W 1 1 i hΔ)
      (Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom)) ≫
        (transportedAdditionRingIso W 1 1 i hΔ).inv) ≫
          Spec.map (CommRingCat.ofHom (transportedAdditionInput W 1 1 i).toRingHom) =
      pullback.snd (transportedPolynomialDomainMap W 1 1 i hΔ)
        (Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom) := by
  rw [Category.assoc, transportedAdditionRingIso_inv_input]
  exact pullback.condition

/-- The actual full scheme intersection maps to the integral output overlap. -/
def infinityTransportedSchemeOutput : InfinityTransportedScheme W i hΔ ⟶
    Spec (CommRingCat.of (Overlap W (additionChartOutput i) 1)) :=
  infinityTransportedCommonOutput W i
    (pullback.fst _ _ ≫ (transportedAdditionRingIso W 1 1 i hΔ).inv)
    (pullback.snd _ _) (infinityTransportedScheme_inputs W i hΔ)

/-- Its first projection is the affine addition map already attached to this cover member. -/
theorem infinityTransportedSchemeOutput_affine :
    infinityTransportedSchemeOutput W i hΔ ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W (additionChartOutput i) 1).toRingHom) =
      pullback.fst _ _ ≫ affineOverlapAdditionSpec W 1 1 hΔ i := by
  rw [infinityTransportedSchemeOutput, infinityTransportedCommonOutput_affine]
  simp only [Category.assoc, affineOverlapAdditionSpec]
  rw [← Category.assoc (transportedAdditionRingIso W 1 1 i hΔ).inv,
    transportedAdditionRingIso_inv_affine]

/-- Its second projection is the existing infinity law, on the entire common domain. -/
theorem infinityTransportedSchemeOutput_infinity :
    infinityTransportedSchemeOutput W i hΔ ≫
        Spec.map (CommRingCat.ofHom (transitionBase W (additionChartOutput i) 1).toRingHom) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (infinityAdditionChart W).toRingHom) :=
  infinityTransportedCommonOutput_infinity W i _ _ _

end FLT.Mazur.WeierstrassIntegralChart
