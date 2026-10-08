/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassTransportedPolynomialComparison

/-!
# Scheme compatibility of transported affine and polynomial addition

The algebraic output factorization is transported to the actual fiber product
of a member of the existing affine cover and an original polynomial output
open. Its two projections recover the already constructed scheme morphisms.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (j k : Fin 3)
  (i : AdditionChartIndex) (t : Fin 3)

variable {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of (TransportedAdditionRing W j k i)))
  (g : X ⟶ Spec (CommRingCat.of (AdditionOutputOpen W j k t)))
  (h : f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionInput W j k i).toRingHom) =
    g ≫ Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom))

/-- Any common scheme over the two domains maps into the concrete output overlap. -/
def transportedPolynomialCommonOutput :
    X ⟶ Spec (CommRingCat.of (Overlap W t (additionChartOutput i))) :=
  (transportedPolynomialIntersection_isPullback W j k i t).lift f g h ≫
    Spec.map (CommRingCat.ofHom (transportedPolynomialOutputLift W j k i t).toRingHom)

/-- The polynomial projection of the common output is the original polynomial law. -/
theorem transportedPolynomialCommonOutput_polynomial :
    transportedPolynomialCommonOutput W j k i t f g h ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W t (additionChartOutput i)).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (transportedPolynomialOutputLift W j k i t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W t (additionChartOutput i)).toRingHom) =
      Spec.map (CommRingCat.ofHom (transportedPolynomialOutput W j k i t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun a => Spec.map (CommRingCat.ofHom a.toRingHom))
      (transportedPolynomialOutputLift_restriction W j k i t)
  rw [transportedPolynomialCommonOutput, Category.assoc, he, ← Category.assoc,
    IsPullback.lift_snd]

/-- The affine projection of the common output is the transported affine law. -/
theorem transportedPolynomialCommonOutput_affine :
    transportedPolynomialCommonOutput W j k i t f g h ≫
        Spec.map (CommRingCat.ofHom (transitionBase W t (additionChartOutput i)).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (transportedAdditionAffine W j k i).toRingHom) ≫
        additionChartSpec W i := by
  have he : Spec.map (CommRingCat.ofHom (transportedPolynomialOutputLift W j k i t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W t (additionChartOutput i)).toRingHom) =
      Spec.map (CommRingCat.ofHom (transportedPolynomialRestriction W j k i t).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transportedAdditionAffine W j k i).toRingHom) ≫
          additionChartSpec W i := by
    rw [← additionChartAlgOutput_spec, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun a => Spec.map (CommRingCat.ofHom a.toRingHom))
      (transportedPolynomialOutputLift_transition W j k i t)
  rw [transportedPolynomialCommonOutput, Category.assoc, he, ← Category.assoc,
    IsPullback.lift_fst]

variable (hΔ : IsUnit W.Δ)

/-- Inclusion of a transported cover member into its original input-chart product. -/
def transportedPolynomialDomainMap : (affineOverlapAdditionCover W j k hΔ).X i ⟶
    Spec (CommRingCat.of (ChartProduct W j k)) :=
  (affineOverlapAdditionCover W j k hΔ).f i ≫
    Spec.map (CommRingCat.ofHom (productOverlapRestriction W j k 2 2).toRingHom)

/-- The ring identification retains the original input-product inclusion. -/
theorem transportedAdditionRingIso_inv_input :
    (transportedAdditionRingIso W j k i hΔ).inv ≫
        Spec.map (CommRingCat.ofHom (transportedAdditionInput W j k i).toRingHom) =
      transportedPolynomialDomainMap W j k i hΔ := by
  change (transportedAdditionRing_isPullback W j k i).isoPullback.inv ≫
    Spec.map (CommRingCat.ofHom ((transportedAdditionOverlap W j k i).comp
      (productOverlapRestriction W j k 2 2)).toRingHom) = _
  rw [show ((transportedAdditionOverlap W j k i).comp
      (productOverlapRestriction W j k 2 2)).toRingHom =
    (transportedAdditionOverlap W j k i).toRingHom.comp
      (productOverlapRestriction W j k 2 2).toRingHom from rfl,
    CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc, IsPullback.isoPullback_inv_fst]
  rfl

/-- The ring identification retains the projection to the affine addition domain. -/
theorem transportedAdditionRingIso_inv_affine :
    (transportedAdditionRingIso W j k i hΔ).inv ≫
        Spec.map (CommRingCat.ofHom (transportedAdditionAffine W j k i).toRingHom) =
      affineOverlapAdditionProjection W j k hΔ i :=
  (transportedAdditionRing_isPullback W j k i).isoPullback_inv_snd

/-- The actual intersection of a transported cover member and an original polynomial domain. -/
abbrev TransportedPolynomialScheme := pullback (transportedPolynomialDomainMap W j k i hΔ)
  (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom))

/-- The original inputs agree on the actual scheme intersection. -/
theorem transportedPolynomialScheme_inputs :
    (pullback.fst (transportedPolynomialDomainMap W j k i hΔ)
      (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)) ≫
        (transportedAdditionRingIso W j k i hΔ).inv) ≫
          Spec.map (CommRingCat.ofHom (transportedAdditionInput W j k i).toRingHom) =
      pullback.snd (transportedPolynomialDomainMap W j k i hΔ)
        (Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (additionOutputRestriction W j k t).toRingHom) := by
  rw [Category.assoc, transportedAdditionRingIso_inv_input]
  exact pullback.condition

/-- Output overlap on the actual transported-affine/polynomial scheme intersection. -/
def transportedPolynomialSchemeOutput : TransportedPolynomialScheme W j k i t hΔ ⟶
    Spec (CommRingCat.of (Overlap W t (additionChartOutput i))) :=
  transportedPolynomialCommonOutput W j k i t
    (pullback.fst _ _ ≫ (transportedAdditionRingIso W j k i hΔ).inv)
    (pullback.snd _ _) (transportedPolynomialScheme_inputs W j k i t hΔ)

/-- The polynomial projection on the actual intersection recovers the original law. -/
theorem transportedPolynomialSchemeOutput_polynomial :
    transportedPolynomialSchemeOutput W j k i t hΔ ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W t (additionChartOutput i)).toRingHom) =
      pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (projectiveAdditionChart W j k t).toRingHom) :=
  transportedPolynomialCommonOutput_polynomial W j k i t _ _ _

/-- The other projection recovers the existing transported affine addition morphism. -/
theorem transportedPolynomialSchemeOutput_affine :
    transportedPolynomialSchemeOutput W j k i t hΔ ≫
        Spec.map (CommRingCat.ofHom (transitionBase W t (additionChartOutput i)).toRingHom) =
      pullback.fst _ _ ≫ affineOverlapAdditionSpec W j k hΔ i := by
  rw [transportedPolynomialSchemeOutput, transportedPolynomialCommonOutput_affine]
  simp only [Category.assoc, affineOverlapAdditionSpec]
  rw [← Category.assoc (transportedAdditionRingIso W j k i hΔ).inv,
    transportedAdditionRingIso_inv_affine]

end FLT.Mazur.WeierstrassIntegralChart
