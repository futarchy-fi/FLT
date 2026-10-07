/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassMixedOutputComparison
public import FLT.Mazur.WeierstrassSameOutputIntersections

/-!
# Mixed output compatibility on actual transported scheme intersections

All four ordinary/reciprocal intersections map to the integral Y/Z output
overlap. Its two projections recover the original local addition maps.
The construction applies to arbitrary common schemes and hence to the
actual fiber products of the transported addition opens.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b c : Bool)

/-- On the concrete mixed intersection, addition factors through the output overlap. -/
def mixedIntersectionOutput :
    Overlap W 1 2 →ₐ[R] AdditionIntersection W (ordinaryIndex b) (reciprocalIndex c) :=
  mixedOutputLift W b c (additionIntersectionLeft W _ _) (additionIntersectionRight W _ _)
    (additionIntersection_inputs W _ _)

variable {X : Scheme}
  (f : X ⟶ Spec (additionChartRing W (ordinaryIndex b)))
  (g : X ⟶ Spec (additionChartRing W (reciprocalIndex c)))
  (hfg : f ≫ additionChartInclusion W (ordinaryIndex b) =
    g ≫ additionChartInclusion W (reciprocalIndex c))

/-- The universal mixed comparison for any scheme with the same two affine inputs. -/
def mixedCommonOutput : X ⟶ Spec (CommRingCat.of (Overlap W 1 2)) :=
  (additionIntersection_isPullback W (ordinaryIndex b) (reciprocalIndex c)).lift f g hfg ≫
    Spec.map (CommRingCat.ofHom (mixedIntersectionOutput W b c).toRingHom)

/-- The common output restricts to the original reciprocal addition map. -/
@[reassoc] theorem mixedCommonOutput_reciprocal :
    mixedCommonOutput W b c f g hfg ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (mixedIntersectionOutput W b c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom) =
      Spec.map (CommRingCat.ofHom (additionIntersectionRight W _ _).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (mixedOutputLift_restriction W b c _ _ (additionIntersection_inputs W _ _))
  rw [mixedCommonOutput, Category.assoc, he, ← Category.assoc, IsPullback.lift_snd]

/-- The common output changes charts to the original ordinary addition map. -/
@[reassoc] theorem mixedCommonOutput_ordinary :
    mixedCommonOutput W b c f g hfg ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) =
      f ≫ Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (mixedIntersectionOutput W b c).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) =
      Spec.map (CommRingCat.ofHom (additionIntersectionLeft W _ _).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom))
      (mixedOutputLift_transition W b c _ _ (additionIntersection_inputs W _ _))
  rw [mixedCommonOutput, Category.assoc, he, ← Category.assoc, IsPullback.lift_fst]

variable (j k : Fin 3) (hΔ : IsUnit W.Δ)

/-- The overlap-valued output on the actual transported ordinary/reciprocal intersection. -/
def transportedMixedOutput :
    pullback ((affineOverlapAdditionCover W j k hΔ).f (ordinaryIndex b))
      ((affineOverlapAdditionCover W j k hΔ).f (reciprocalIndex c)) ⟶
        Spec (CommRingCat.of (Overlap W 1 2)) :=
  mixedCommonOutput W b c
    (pullback.fst _ _ ≫ affineOverlapAdditionProjection W j k hΔ (ordinaryIndex b))
    (pullback.snd _ _ ≫ affineOverlapAdditionProjection W j k hΔ (reciprocalIndex c))
    (by simpa only [Category.assoc] using
      transportedAdditionIntersection_inputs W j k hΔ (ordinaryIndex b) (reciprocalIndex c))

/-- The Y-output projection is the transported reciprocal law on its actual intersection. -/
@[reassoc] theorem transportedMixedOutput_reciprocal :
    transportedMixedOutput W b c j k hΔ ≫
        Spec.map (CommRingCat.ofHom (overlapRestriction W 1 2).toRingHom) =
      pullback.snd _ _ ≫ affineOverlapAdditionProjection W j k hΔ (reciprocalIndex c) ≫
        Spec.map (CommRingCat.ofHom (reciprocalChartAddition W c).toRingHom) := by
  exact (mixedCommonOutput_reciprocal W b c _ _ _).trans (Category.assoc _ _ _)

/-- The Z-output projection is the transported ordinary law on its actual intersection. -/
@[reassoc] theorem transportedMixedOutput_ordinary :
    transportedMixedOutput W b c j k hΔ ≫
        Spec.map (CommRingCat.ofHom (transitionBase W 1 2).toRingHom) =
      pullback.fst _ _ ≫ affineOverlapAdditionProjection W j k hΔ (ordinaryIndex b) ≫
        Spec.map (CommRingCat.ofHom (ordinaryChartAddition W b).toRingHom) := by
  exact (mixedCommonOutput_ordinary W b c _ _ _).trans (Category.assoc _ _ _)

end FLT.Mazur.WeierstrassIntegralChart
