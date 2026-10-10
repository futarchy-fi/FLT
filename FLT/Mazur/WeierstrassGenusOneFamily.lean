/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicGenus
public import FLT.Mazur.WeierstrassSmoothFiberCore
public import FLT.Mazur.StructureCohomologyOverIso
public import FLT.Mazur.ClassifiedGenusOneFamily

/-!
# The actual smooth Weierstrass family has genus-one fibers

Coefficient base change and cohomology transport compute H1 on every
field-valued Cartesian square. Together with the existing smooth classified
core and constant functions, this constructs the genus-one family interface
for the original unit-discriminant Weierstrass model.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve FLT.Mazur.FCurve.CurveFiberHypotheses

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- Every field-valued fiber square has one-dimensional actual first cohomology. -/
theorem integralCurveFieldSquareH1_finrank {K : Type} [Field K]
    (s : Spec (.of K) ⟶ Spec (.of R)) {Y : Scheme}
    (fst : Y ⟶ integralCurve W) (snd : Y ⟶ Spec (.of K))
    (h : IsPullback fst snd (integralCurveStructure W) s) :
    Module.finrank K (H1 snd) = 1 := by
  let _ := (Spec.preimage s).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap R K)) = s := Spec.map_preimage s
  have hc : IsPullback (integralCoefficientMorphism (S := K) W)
      (integralCurveStructure (W.map (algebraMap R K))) (integralCurveStructure W) s := by
    simpa only [hb] using (integralCoefficient_isPullback (S := K) W)
  let e := hc.isoIsPullback _ _ h
  have he : e.hom ≫ snd = integralCurveStructure (W.map (algebraMap R K)) :=
    hc.isoIsPullback_hom_snd _ _ _
  exact (structureScalarH_finrank_of_overIso e snd _ he 1).trans
    (integralCurveH1_finrank (W.map (algebraMap R K)))

/-- Every geometric fiber of the actual smooth cubic satisfies the genus-one contract. -/
theorem integralCurve_genusOneGeometricFibers (hΔ : IsUnit W.Δ) :
    NodalGenusOneGeometricFibers (integralCurveStructure W) := by
  constructor
  intro K _ _ s Y fst snd h
  let _ : IsProper snd := MorphismProperty.of_isPullback h inferInstance
  refine ⟨((integralCurve_classifiedGeometricFibers W hΔ).fiber K s fst snd h).toNodalFiberCore,
    integralCurveFieldSquare_constantGlobalSections W s fst snd h, ?_⟩
  exact integralCurveFieldSquareH1_finrank W s fst snd h

/-- Unit discriminant gives the full classified genus-one family on the original model. -/
theorem integralCurve_classifiedGenusOneFamily (hΔ : IsUnit W.Δ) :
    ClassifiedGenusOneFamily (integralCurveStructure W) :=
  ⟨(integralCurve_classifiedFamilyCore W hΔ).family,
    integralCurve_classifiedGeometricFibers W hΔ, integralCurve_genusOneGeometricFibers W hΔ⟩

/-- The constructed genus-one family persists under arbitrary scheme base change. -/
theorem integralCurve_classifiedGenusOneFamily_baseChange (hΔ : IsUnit W.Δ)
    {T : Scheme} (g : T ⟶ Spec (.of R)) :
    ClassifiedGenusOneFamily (pullback.snd (integralCurveStructure W) g) :=
  (integralCurve_classifiedGenusOneFamily W hΔ).baseChange g

end FLT.Mazur.WeierstrassIntegralChart
