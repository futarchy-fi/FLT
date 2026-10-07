/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAdditionIntersections
public import FLT.Mazur.WeierstrassAdditionChartCompatibility

/-!
# Addition compatibility on actual same-output intersections

The ordinary pair and the reciprocal pair agree on their tensor intersections.
The universal property then gives equality on any scheme over both domains,
including intersections of the transported addition opens.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Algebraic equality on the concrete intersection implies equality on any common scheme. -/
theorem additionIntersection_compare (i j : AdditionChartIndex)
    {T : Type u} [CommRing T] [Algebra R T]
    (a : T →ₐ[R] additionChartRing W i) (b : T →ₐ[R] additionChartRing W j)
    (hab : (additionIntersectionLeft W i j).comp a =
      (additionIntersectionRight W i j).comp b)
    {X : Scheme} (f : X ⟶ Spec (additionChartRing W i))
    (g : X ⟶ Spec (additionChartRing W j))
    (hfg : f ≫ additionChartInclusion W i = g ≫ additionChartInclusion W j) :
    f ≫ Spec.map (CommRingCat.ofHom a.toRingHom) =
      g ≫ Spec.map (CommRingCat.ofHom b.toRingHom) := by
  have he : Spec.map (CommRingCat.ofHom (additionIntersectionLeft W i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) =
      Spec.map (CommRingCat.ofHom (additionIntersectionRight W i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom b.toRingHom) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun h => Spec.map (CommRingCat.ofHom h.toRingHom)) hab
  have hp := additionIntersection_isPullback W i j
  have h := congrArg (fun k => hp.lift f g hfg ≫ k) he
  simpa only [← Category.assoc, hp.lift_fst, hp.lift_snd] using h

/-- Ordinary secant and tangent maps agree on every scheme over both domains. -/
theorem ordinaryAddition_commonScheme {X : Scheme}
    (f : X ⟶ Spec (additionChartRing W .secant))
    (g : X ⟶ Spec (additionChartRing W .tangent))
    (hfg : f ≫ additionChartInclusion W .secant = g ≫ additionChartInclusion W .tangent) :
    f ≫ additionChartSpec W .secant = g ≫ additionChartSpec W .tangent := by
  apply additionIntersection_compare W .secant .tangent (secantAddition W) (tangentAddition W)
    _ f g hfg
  exact addition_chart_compatibility W _ _ (additionIntersection_inputs W .secant .tangent)

/-- Reciprocal secant and tangent maps agree on every scheme over both domains. -/
theorem reciprocalAddition_commonScheme {X : Scheme}
    (f : X ⟶ Spec (additionChartRing W .verticalSecant))
    (g : X ⟶ Spec (additionChartRing W .verticalTangent))
    (hfg : f ≫ additionChartInclusion W .verticalSecant =
      g ≫ additionChartInclusion W .verticalTangent) :
    f ≫ additionChartSpec W .verticalSecant = g ≫ additionChartSpec W .verticalTangent := by
  apply additionIntersection_compare W .verticalSecant .verticalTangent
    (verticalSecantAddition W) (verticalTangentAddition W) _ f g hfg
  exact verticalAddition_chart_compatibility W _ _
    (additionIntersection_inputs W .verticalSecant .verticalTangent)

variable (j k : Fin 3) (hΔ : IsUnit W.Δ)

/-- Projection to original domains on a transported intersection has common affine inputs. -/
theorem transportedAdditionIntersection_inputs (a b : AdditionChartIndex) :
    pullback.fst ((affineOverlapAdditionCover W j k hΔ).f a)
        ((affineOverlapAdditionCover W j k hΔ).f b) ≫
      affineOverlapAdditionProjection W j k hΔ a ≫ additionChartInclusion W a =
    pullback.snd ((affineOverlapAdditionCover W j k hΔ).f a)
        ((affineOverlapAdditionCover W j k hΔ).f b) ≫
      affineOverlapAdditionProjection W j k hΔ b ≫ additionChartInclusion W b := by
  rw [affineOverlapAdditionProjection_inputs, affineOverlapAdditionProjection_inputs]
  exact pullback.condition_assoc _

/-- Ordinary addition agrees on the actual transported secant/tangent intersection. -/
theorem transportedOrdinaryAddition_compatibility :
    pullback.fst ((affineOverlapAdditionCover W j k hΔ).f .secant)
        ((affineOverlapAdditionCover W j k hΔ).f .tangent) ≫
      affineOverlapAdditionSpec W j k hΔ .secant =
    pullback.snd ((affineOverlapAdditionCover W j k hΔ).f .secant)
        ((affineOverlapAdditionCover W j k hΔ).f .tangent) ≫
      affineOverlapAdditionSpec W j k hΔ .tangent := by
  simpa only [affineOverlapAdditionSpec, Category.assoc] using
    ordinaryAddition_commonScheme W
      (pullback.fst _ _ ≫ affineOverlapAdditionProjection W j k hΔ .secant)
      (pullback.snd _ _ ≫ affineOverlapAdditionProjection W j k hΔ .tangent)
      (by simpa only [Category.assoc] using
        transportedAdditionIntersection_inputs W j k hΔ .secant .tangent)

/-- Reciprocal addition agrees on the actual transported vertical-chart intersection. -/
theorem transportedReciprocalAddition_compatibility :
    pullback.fst ((affineOverlapAdditionCover W j k hΔ).f .verticalSecant)
        ((affineOverlapAdditionCover W j k hΔ).f .verticalTangent) ≫
      affineOverlapAdditionSpec W j k hΔ .verticalSecant =
    pullback.snd ((affineOverlapAdditionCover W j k hΔ).f .verticalSecant)
        ((affineOverlapAdditionCover W j k hΔ).f .verticalTangent) ≫
      affineOverlapAdditionSpec W j k hΔ .verticalTangent := by
  simpa only [affineOverlapAdditionSpec, Category.assoc] using
    reciprocalAddition_commonScheme W
      (pullback.fst _ _ ≫ affineOverlapAdditionProjection W j k hΔ .verticalSecant)
      (pullback.snd _ _ ≫ affineOverlapAdditionProjection W j k hΔ .verticalTangent)
      (by simpa only [Category.assoc] using
        transportedAdditionIntersection_inputs W j k hΔ .verticalSecant .verticalTangent)

end FLT.Mazur.WeierstrassIntegralChart
