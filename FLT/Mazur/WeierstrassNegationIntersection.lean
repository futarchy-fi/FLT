/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNegationOverlap
public import FLT.Mazur.WeierstrassNegationCover
public import FLT.Mazur.WeierstrassIntegralProductOverlap
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# The actual intersection of the two negation domains

Localize the infinity neighborhood at the original Z coordinate. Its spectrum
represents the common input domain, and its explicit output overlap proves
compatibility for arbitrary schemes mapping into both negation domains.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The concrete intersection of the infinity negation neighborhood and affine overlap. -/
abbrev NegationIntersection :=
  Localization.Away (infinityNegationRestriction W (coord W 1 2))

/-- Restriction from the infinity negation neighborhood. -/
def negationIntersectionFirst : InfinityNegationOpen W →ₐ[R] NegationIntersection W :=
  IsScalarTower.toAlgHom R _ _

/-- The second input coordinate is invertible on the intersection. -/
theorem negationIntersection_z_isUnit :
    IsUnit (((negationIntersectionFirst W).comp (infinityNegationRestriction W))
      (coord W 1 2)) :=
  IsLocalization.Away.algebraMap_isUnit (infinityNegationRestriction W (coord W 1 2))

/-- Restriction from the original Y/Z overlap. -/
def negationIntersectionSecond : Overlap W 1 2 →ₐ[R] NegationIntersection W :=
  overlapLift W 1 2 ((negationIntersectionFirst W).comp (infinityNegationRestriction W))
    (negationIntersection_z_isUnit W)

/-- Both restrictions retain exactly the same original Y-chart input. -/
theorem negationIntersection_inputs :
    (negationIntersectionSecond W).comp (overlapRestriction W 1 2) =
      (negationIntersectionFirst W).comp (infinityNegationRestriction W) :=
  overlapLift_restriction ..

/-- The concrete intersection has the actual scheme pullback universal property. -/
theorem negationIntersection_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (negationIntersectionFirst W).toRingHom))
      (Spec.map (CommRingCat.ofHom (negationIntersectionSecond W).toRingHom))
      (infinityNegationInclusion W) (overlapInclusion W 1 2) := by
  have : IsLocalization ((Submonoid.powers (coord W 1 2)).map
      (infinityNegationRestriction W).toRingHom) (NegationIntersection W) := by
    rw [Submonoid.map_powers]
    infer_instance
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_of_isLocalization (infinityNegationRestriction W).toRingHom
    (negationIntersectionSecond W).toRingHom
    (congrArg AlgHom.toRingHom (negationIntersection_inputs W))
    (Submonoid.powers (coord W 1 2))

/-- Negation on the intersection maps to the actual output Y/Z overlap. -/
def negationIntersectionOutput : Overlap W 1 2 →ₐ[R] NegationIntersection W :=
  negationOverlapLift W (negationIntersectionFirst W) (negationIntersectionSecond W)
    (negationIntersection_inputs W).symm

/-- Both local outputs agree as morphisms into the glued cubic on the intersection. -/
theorem negationIntersection_curve_eq :
    Spec.map (CommRingCat.ofHom (negationIntersectionFirst W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (infinityNegationChart W).toRingHom) ≫
          integralCurveChart W 1 =
      Spec.map (CommRingCat.ofHom (negationIntersectionSecond W).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) ≫
          Spec.map (CommRingCat.ofHom (affineNegation W).toRingHom) ≫
            integralCurveChart W 2 := by
  simp only [← Category.assoc]
  apply integralCurve_output_eq W 1 2 _ _
    (Spec.map (CommRingCat.ofHom (negationIntersectionOutput W).toRingHom))
  · change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (negationOverlapLift_restriction W _ _ (negationIntersection_inputs W).symm)
  · change Spec.map _ ≫ Spec.map _ = (Spec.map _ ≫ Spec.map _) ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f => Spec.map (CommRingCat.ofHom f.toRingHom))
      (negationOverlapLift_transition W _ _ (negationIntersection_inputs W).symm)

/-- Common schemes with equal global inputs have equal negation outputs. -/
theorem negation_commonScheme {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (InfinityNegationOpen W))) (g : X ⟶ chartScheme W 2)
    (h : f ≫ infinityNegationInclusion W ≫ integralCurveChart W 1 =
      g ≫ integralCurveChart W 2) :
    f ≫ Spec.map (CommRingCat.ofHom (infinityNegationChart W).toRingHom) ≫
        integralCurveChart W 1 =
      g ≫ Spec.map (CommRingCat.ofHom (affineNegation W).toRingHom) ≫
        integralCurveChart W 2 := by
  obtain ⟨a, ha, hb⟩ := (integralCurveChart_overlap_isPullback W 1 2).exists_lift
    (f ≫ infinityNegationInclusion W) g (by simpa only [Category.assoc] using h)
  obtain ⟨v, hv, hv'⟩ := (negationIntersection_isPullback W).exists_lift f a ha.symm
  have he := congrArg (fun t => v ≫ t) (negationIntersection_curve_eq W)
  simpa only [← Category.assoc, hv, hv', hb] using he

end FLT.Mazur.WeierstrassIntegralChart
