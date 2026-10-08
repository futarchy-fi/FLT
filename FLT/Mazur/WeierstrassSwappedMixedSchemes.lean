/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSwappedSameOutputSchemes
public import FLT.Mazur.WeierstrassIntegralCurveMorphisms

/-!
# Mixed outputs on actual reversed-input scheme intersections

All four ordinary/reciprocal intersections map to the integral Y/Z output
overlap. Its two projections recover the original local addition maps.
The construction applies to arbitrary common schemes and hence to the
actual fiber products of the original and reversed addition opens.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- On the concrete mixed intersection, addition factors through the output overlap. -/
def swappedMixedIntersectionOutput :
    Overlap W 1 2 →ₐ[R] SwappedAdditionIntersection W (ordinaryIndex b) (reciprocalIndex c) :=
  swappedMixedOutputLift W b c (swappedAdditionLeft W _ _) (swappedAdditionRight W _ _)
    (swappedAddition_inputs W _ _)

variable {X : Scheme}
  (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
  (g : X ⟶ Spec (additionChartRing W (reciprocalIndex c)))
  (hfg : f ≫ additionChartInclusion W (ordinaryIndex b) =
    g ≫ additionChartInclusion W (reciprocalIndex c) ≫ affineInputSwap W)

/-- The universal mixed comparison for any scheme with the same two affine inputs. -/
def swappedMixedCommonOutput : X ⟶ Spec (CommRingCat.of (Overlap W 1 2)) :=
  (swappedAddition_isPullback W (ordinaryIndex b) (reciprocalIndex c)).lift f g
    (by simpa only [Category.assoc] using hfg) ≫
    Spec.map (CommRingCat.ofHom (swappedMixedIntersectionOutput W b c).toRingHom)

/-- The common output restricts to the original reciprocal addition map. -/
@[reassoc] theorem swappedMixedCommonOutput_reciprocal :
    swappedMixedCommonOutput W b c f g hfg ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (swappedMixedIntersectionOutput W b c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom) =
      Spec.map (CommRingCat.ofHom (swappedAdditionRight W _ _).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (swappedMixedOutputLift_restriction W b c _ _ (swappedAddition_inputs W _ _))
  rw [swappedMixedCommonOutput, Category.assoc, he, ← Category.assoc, IsPullback.lift_snd]

/-- The common output changes charts to the original ordinary addition map. -/
@[reassoc] theorem swappedMixedCommonOutput_ordinary :
    swappedMixedCommonOutput W b c f g hfg ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (swappedMixedIntersectionOutput W b c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) =
      Spec.map (CommRingCat.ofHom (swappedAdditionLeft W _ _).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (swappedMixedOutputLift_transition W b c _ _ (swappedAddition_inputs W _ _))
  rw [swappedMixedCommonOutput, Category.assoc, he, ← Category.assoc, IsPullback.lift_fst]

include hfg in
/-- Mixed reversed-input outputs coincide in the glued projective cubic. -/
theorem mixedAddition_swap_curve_eq :
    (f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom)) ≫
        integralCurveChart W 2 =
      (g ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom)) ≫
        integralCurveChart W 1 := by
  exact (integralCurve_output_eq W 1 2 _ _ (swappedMixedCommonOutput W b c f g hfg)
    (swappedMixedCommonOutput_reciprocal W b c f g hfg)
    (swappedMixedCommonOutput_ordinary W b c f g hfg)).symm

end FLT.Mazur.WeierstrassIntegralChart
