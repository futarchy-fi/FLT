/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralCurveProduct

/-!
# Concrete intersections of charts in the integral cubic product

Tensor products of the normalized coordinate overlaps represent the actual
intersections in the glued curve product. This identifies the domains on which
cross-input addition comparisons must be checked.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.ProjectiveSpace

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The spectrum of the algebra restriction is the original chart-overlap inclusion. -/
theorem overlapRestriction_spec (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (overlapRestriction W j k).toRingHom) =
      overlapInclusion W j k := rfl

/-- The normalized other restriction is the gluing transition followed by inclusion. -/
theorem chartOverlapOther_transition (j k : Fin 3) :
    Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom) =
      chartTransition W j k ≫ overlapInclusion W k j := by
  apply (cancel_mono (integralCurveChart W k)).mp
  rw [integralCurve_output_transition, Category.assoc, integralCurveChart_compatibility]

/-- The original algebraic overlap is the actual intersection of the glued charts. -/
theorem integralCurveChart_overlap_isPullback (j k : Fin 3) :
    IsPullback (overlapInclusion W j k)
      (Spec.map (CommRingCat.ofHom (transitionBase W j k).toRingHom))
      (integralCurveChart W j) (integralCurveChart W k) := by
  rw [chartOverlapOther_transition]
  exact IsPullback.of_isLimit ((integralCurveGlueData W).vPullbackConeIsLimit ⟨j⟩ ⟨k⟩)

variable (b c d e : Bool)

/-- Restriction of the simultaneous overlap to the first input product. -/
abbrev integralProductOverlapFst := Spec.map (CommRingCat.ofHom
  (productOverlapRestriction W (productChartCoordinate b) (productChartCoordinate c)
    (productChartCoordinate d) (productChartCoordinate e)).toRingHom)

/-- Restriction of the simultaneous overlap to the second input product. -/
abbrev integralProductOverlapSnd := Spec.map (CommRingCat.ofHom
  (productOverlapOther W (productChartCoordinate b) (productChartCoordinate c)
    (productChartCoordinate d) (productChartCoordinate e)).toRingHom)

/-- The two normalizations of a common input pair agree in the actual global product. -/
theorem integralProductOverlap_condition :
    integralProductOverlapFst W b c d e ≫ integralCurveProductChart W b c =
      integralProductOverlapSnd W b c d e ≫ integralCurveProductChart W d e := by
  apply pullback.hom_ext
  · simp only [Category.assoc, integralCurveProductChart_fst, integralProductOverlapFst,
      integralProductOverlapSnd, productOverlapRestriction, productOverlapOther,
      chartProductLeft, Algebra.TensorProduct.includeLeft, tensorSpecMap_fst_assoc,
      integralCurve_output_transition, overlapRestriction_spec]
  · simp only [Category.assoc, integralCurveProductChart_snd, integralProductOverlapFst,
      integralProductOverlapSnd, productOverlapRestriction, productOverlapOther,
      chartProductRight, tensorSpecMap_snd_assoc,
      integralCurve_output_transition, overlapRestriction_spec]

/-- A compatible pair of input maps lifts to the tensor of their coordinate intersections. -/
theorem integralProductOverlap_exists_lift {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate b) (productChartCoordinate c))))
    (g : X ⟶ Spec (.of (ChartProduct W (productChartCoordinate d) (productChartCoordinate e))))
    (h : f ≫ integralCurveProductChart W b c = g ≫ integralCurveProductChart W d e) :
    ∃ v : X ⟶ Spec (.of (ProductOverlap W (productChartCoordinate b) (productChartCoordinate c)
      (productChartCoordinate d) (productChartCoordinate e))),
      v ≫ integralProductOverlapFst W b c d e = f ∧
        v ≫ integralProductOverlapSnd W b c d e = g := by
  let j := productChartCoordinate b
  let k := productChartCoordinate c
  let j' := productChartCoordinate d
  let k' := productChartCoordinate e
  have hl : (f ≫ tensorSpecFst R (Coordinate W j) (Coordinate W k)) ≫
      integralCurveChart W j =
      (g ≫ tensorSpecFst R (Coordinate W j') (Coordinate W k')) ≫
        integralCurveChart W j' := by
    simpa only [Category.assoc, integralCurveProductChart_fst, chartProductLeft,
      Algebra.TensorProduct.includeLeft, tensorSpecFst, j, k, j', k'] using
      congrArg (fun a => a ≫ pullback.fst (integralCurveStructure W) (integralCurveStructure W)) h
  have hr : (f ≫ tensorSpecSnd R (Coordinate W j) (Coordinate W k)) ≫
      integralCurveChart W k =
      (g ≫ tensorSpecSnd R (Coordinate W j') (Coordinate W k')) ≫
        integralCurveChart W k' := by
    simpa only [Category.assoc, integralCurveProductChart_snd, chartProductRight,
      tensorSpecSnd, j, k, j', k'] using
      congrArg (fun a => a ≫ pullback.snd (integralCurveStructure W) (integralCurveStructure W)) h
  obtain ⟨a, ha, ha'⟩ := (integralCurveChart_overlap_isPullback W j j').exists_lift _ _ hl
  obtain ⟨z, hz, hz'⟩ := (integralCurveChart_overlap_isPullback W k k').exists_lift _ _ hr
  have haz : a ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Overlap W j j'))) =
      z ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Overlap W k k'))) := by
    rw [← specAlgHom_base R (overlapRestriction W j j'),
      ← specAlgHom_base R (overlapRestriction W k k'),
      ← Category.assoc, overlapRestriction_spec, ha,
      ← Category.assoc, overlapRestriction_spec, hz, Category.assoc, Category.assoc]
    exact congrArg (fun a => f ≫ a) (tensorSpecIsPullback R (Coordinate W j) (Coordinate W k)).w
  obtain ⟨v, hv, hv'⟩ := (tensorSpecIsPullback R (Overlap W j j') (Overlap W k k')).exists_lift
    _ _ haz
  refine ⟨v, ?_, ?_⟩
  · apply (tensorSpecIsPullback R (Coordinate W j) (Coordinate W k)).hom_ext
    · rw [Category.assoc, integralProductOverlapFst, productOverlapRestriction,
        tensorSpecMap_fst, ← Category.assoc, hv, overlapRestriction_spec, ha]
    · rw [Category.assoc, integralProductOverlapFst, productOverlapRestriction,
        tensorSpecMap_snd, ← Category.assoc, hv', overlapRestriction_spec, hz]
  · apply (tensorSpecIsPullback R (Coordinate W j') (Coordinate W k')).hom_ext
    · rw [Category.assoc, integralProductOverlapSnd, productOverlapOther,
        tensorSpecMap_fst, ← Category.assoc, hv, ha']
    · rw [Category.assoc, integralProductOverlapSnd, productOverlapOther,
        tensorSpecMap_snd, ← Category.assoc, hv', hz']

/-- The concrete tensor overlap has the universal property of the global intersection. -/
theorem integralProductOverlap_isPullback :
    IsPullback (integralProductOverlapFst W b c d e) (integralProductOverlapSnd W b c d e)
      (integralCurveProductChart W b c) (integralCurveProductChart W d e) := by
  have h (s : PullbackCone (integralCurveProductChart W b c) (integralCurveProductChart W d e)) :=
    integralProductOverlap_exists_lift W b c d e s.fst s.snd s.condition
  choose lift hl hr using h
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (integralProductOverlap_condition W b c d e) lift hl hr ?_)
  intro s m hm _
  exact (cancel_mono (integralProductOverlapFst W b c d e)).mp (hm.trans (hl s).symm)

end FLT.Mazur.WeierstrassIntegralChart
