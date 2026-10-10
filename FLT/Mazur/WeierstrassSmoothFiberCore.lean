/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGeometricIntegral
public import FLT.Mazur.WeierstrassIntegralProper
public import FLT.Mazur.WeierstrassIntegralSmooth
public import FLT.Mazur.SmoothCurveDimension
public import FLT.Mazur.DRFiberClassification

/-!
# The actual smooth Weierstrass family's geometric fiber core

A unit discriminant gives smooth fibers of relative dimension one. Their
proved geometric integrality supplies nonemptiness, connectedness and
reducedness. Each fiber has a single irreducible component of dimension one.
This constructs the existing classified family core; genus remains separate.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve FLT.Mazur.FCurve.CurveFiberHypotheses
open FLT.Mazur.FCurve.DRFiberClassification

namespace FLT.Mazur.WeierstrassIntegralChart

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Every field-valued fiber square of a unit-discriminant cubic has dimension one. -/
theorem integralCurveFieldSquare_dimension (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Spec (.of R)) {Y : Scheme.{u}}
    (fst : Y ⟶ integralCurve W) (snd : Y ⟶ Spec (.of K))
    (h : IsPullback fst snd (integralCurveStructure W) s) : topologicalKrullDim Y = 1 := by
  let _ := integralCurveStructure_smooth_dimension W hΔ
  let _ : SmoothOfRelativeDimension 1 snd := MorphismProperty.of_isPullback h inferInstance
  let _ := integralCurveFieldSquare_isIntegral W s fst snd h
  exact smoothCurveDimension snd inferInstance inferInstance

/-- Each actual smooth fiber has pure dimension one, tested on its irreducible components. -/
theorem integralCurveFieldSquare_pureDimension (hΔ : IsUnit W.Δ) {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Spec (.of R)) {Y : Scheme.{u}}
    (fst : Y ⟶ integralCurve W) (snd : Y ⟶ Spec (.of K))
    (h : IsPullback fst snd (integralCurveStructure W) s) : PureDimensionOne Y := by
  let _ := integralCurveFieldSquare_isIntegral W s fst snd h
  intro Z hZ
  rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hZ
  subst Z
  exact (Homeomorph.Set.univ Y).isHomeomorph.topologicalKrullDim_eq _ |>.trans
    (integralCurveFieldSquare_dimension W hΔ s fst snd h)

/-- Smoothness proves the classification alternative on every actual geometric fiber. -/
theorem integralCurve_classifiedGeometricFibers (hΔ : IsUnit W.Δ) :
    ClassifiedGeometricFibers (integralCurveStructure W) := by
  constructor
  intro K _ _ s Y fst snd h
  let _ := integralCurveStructure_smooth W hΔ
  let _ : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  let _ := integralCurveFieldSquare_isIntegral W s fst snd h
  exact
    { finitePresentation := inferInstance
      nonempty := inferInstance
      connected := inferInstance
      reduced := inferInstance
      pureDimension := integralCurveFieldSquare_pureDimension W hΔ s fst snd h
      nodes := nodes_of_smoothFiber snd
      classification := Or.inl inferInstance }

/-- The existing proper-flat classified family core for the actual smooth cubic. -/
theorem integralCurve_classifiedFamilyCore (hΔ : IsUnit W.Δ) :
    ClassifiedFamilyCore (integralCurveStructure W) :=
  ⟨⟨inferInstance, inferInstance, inferInstance⟩, integralCurve_classifiedGeometricFibers W hΔ⟩

end FLT.Mazur.WeierstrassIntegralChart
