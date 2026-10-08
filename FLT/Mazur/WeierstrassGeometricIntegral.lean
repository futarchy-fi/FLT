/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassIntegralBaseChange
public import FLT.Mazur.WeierstrassIntegralDomain
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometric integrality of every Weierstrass fiber

Arbitrary coefficient base change identifies each field-valued pullback with
the actual cubic of the specialized coefficients. Its proved integrality gives
geometric integrality of the original structure map, even at singular fibers.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Every field-valued coefficient pullback is integral. -/
theorem integralCurveFieldBaseChange_isIntegral (K : Type u) [Field K] [Algebra R K] :
    AlgebraicGeometry.IsIntegral
      (pullback (integralCurveStructure W) (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
  AlgebraicGeometry.IsIntegral.of_isIso (integralCurveCoefficientBaseChangeIso W).hom

/-- Every geometric fiber of the original cubic is integral, without a smoothness hypothesis. -/
instance integralCurveStructure_geometricallyIntegral :
    GeometricallyIntegral (integralCurveStructure W) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  let _ := integralCurveFieldBaseChange_isIntegral W K
  exact AlgebraicGeometry.IsIntegral.of_isIso h.isoPullback.inv

/-- The scheme-theoretic fiber over each prime of the coefficient ring is integral. -/
theorem integralCurveFiber_isIntegral (s : Spec (.of R)) :
    AlgebraicGeometry.IsIntegral ((integralCurveStructure W).fiber s) := inferInstance

/-- Residue-field fibers retain geometric integrality under further field extension. -/
theorem integralCurveFiber_geometricallyIntegral (s : Spec (.of R)) :
    GeometricallyIntegral ((integralCurveStructure W).fiberToSpecResidueField s) := inferInstance

/-- Integrality holds on every field-valued Cartesian square, independently of its presentation. -/
theorem integralCurveFieldSquare_isIntegral {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ Spec (.of R)) {Y : Scheme.{u}}
    (fst : Y ⟶ integralCurve W) (snd : Y ⟶ Spec (.of K))
    (h : IsPullback fst snd (integralCurveStructure W) s) :
    AlgebraicGeometry.IsIntegral Y :=
  GeometricallyIntegral.geometrically_isIntegral s fst snd h

end FLT.Mazur.WeierstrassIntegralChart
