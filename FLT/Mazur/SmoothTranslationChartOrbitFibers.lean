/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertChartRelationPullback
public import FLT.Mazur.VariableHilbertParameterOrbitDescent

/-!
# Exact orbit fibers of the smooth parameter map

The original restricted relation and the full parameter relation give exactly
the same point orbits through the common source. Actual scheme pullbacks
supply the extension points in both directions.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Topology
namespace FLT.Mazur.HilbertChart
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Smooth V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))

omit [Smooth V.hom] in
/-- Original related source points have exactly related parameter images. -/
theorem variableSource_related_iff_chart
    (x y : (variableSourceIntersection f hL d V c).left) :
    Related (smoothHilbertRelationFst f hL) (smoothHilbertRelationSnd f hL)
      ((variableSourceInclusion f hL d V c).left x)
      ((variableSourceInclusion f hL d V c).left y) ↔
    Related (variableChartRelationFst f hL d V c) (variableChartRelationSnd f hL d V c)
      ((variableSourceParameter f hL d V c).left x)
      ((variableSourceParameter f hL d V c).left y) := by
  constructor
  · rintro ⟨a, ha, hb⟩
    obtain ⟨z, hx, hy⟩ := baseOpenRestricted_point_lift f hL d V c x y a ha hb
    refine ⟨(variableRestrictedToChartRelation f hL d V c).left z, ?_, ?_⟩
    · exact (congrArg (fun k ↦ k.left z)
        (variableRestrictedToChartRelation_fst f hL d V c)).trans
          (congrArg (variableSourceParameter f hL d V c).left hx)
    · exact (congrArg (fun k ↦ k.left z)
        (variableRestrictedToChartRelation_snd f hL d V c)).trans
          (congrArg (variableSourceParameter f hL d V c).left hy)
  · rintro ⟨a, ha, hb⟩
    obtain ⟨z, hx, hy⟩ := variableChartBridge_point_lift f hL d V c x y a ha hb
    refine ⟨(variableChartBridgeToOriginal f hL d V c).left z, ?_, ?_⟩
    · exact (congrArg (fun k ↦ k.left z)
        (variableChartBridgeToOriginal_fst f hL d V c)).trans
          (congrArg (variableSourceInclusion f hL d V c).left hx)
    · exact (congrArg (fun k ↦ k.left z)
        (variableChartBridgeToOriginal_snd f hL d V c)).trans
          (congrArg (variableSourceInclusion f hL d V c).left hy)

/-- Equal original orbits on the common source mean related actual parameters. -/
theorem smoothTranslationSourceOrbitMap_eq_iff_chart
    (x y : (variableSourceIntersection f hL d V c).left) :
    smoothTranslationSourceOrbitMap f hL d V c x =
      smoothTranslationSourceOrbitMap f hL d V c y ↔
    Related (variableChartRelationFst f hL d V c) (variableChartRelationSnd f hL d V c)
      ((variableSourceParameter f hL d V c).left x)
      ((variableSourceParameter f hL d V c).left y) := by
  rw [Subtype.ext_iff]
  exact (projection_eq_iff (smoothHilbertEquivalenceRelation f hL) _ _).trans
    (variableSource_related_iff_chart f hL d V c x y)

/-- The map to the actual quotient open identifies precisely the full parameter relation. -/
theorem smoothTranslationChartToOrbit_eq_iff (x y : (variableHilbertTest f d V).left) :
    smoothTranslationChartToOrbit f hL d V c x = smoothTranslationChartToOrbit f hL d V c y ↔
    Related (variableChartRelationFst f hL d V c) (variableChartRelationSnd f hL d V c) x y := by
  obtain ⟨a, rfl⟩ := (variableSourceParameter f hL d V c).left.surjective x
  obtain ⟨b, rfl⟩ := (variableSourceParameter f hL d V c).left.surjective y
  rw [smoothTranslationChartToOrbit_parameter, smoothTranslationChartToOrbit_parameter]
  exact smoothTranslationSourceOrbitMap_eq_iff_chart f hL d V c a b

end FLT.Mazur.HilbertChart
