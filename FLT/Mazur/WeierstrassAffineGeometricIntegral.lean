/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassChartBaseChangeSquare
public import FLT.Mazur.WeierstrassIntegralDomain
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Geometric integrality of the original affine Weierstrass chart

Every field-valued coefficient extension is the actual specialized affine
chart, whose coordinate ring is a domain. In particular this open meets
every fiber of the original cubic, including over nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The affine chart of every coefficient field extension is integral. -/
theorem affineChartFieldBaseChange_isIntegral (K : Type u) [Field K] [Algebra R K] :
    IsIntegral (pullback (chartStructure W 2)
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) :=
  IsIntegral.of_isIso (chartCoefficient_isPullback (S := K) W 2).isoPullback.hom

/-- The original affine open meets every geometric fiber in an integral curve. -/
instance affineChartStructure_geometricallyIntegral :
    GeometricallyIntegral (chartStructure W 2) := by
  constructor
  rw [geometrically_iff_of_commRing]
  intro K _ _ Y fst snd h
  let _ := affineChartFieldBaseChange_isIntegral W K
  exact IsIntegral.of_isIso h.isoPullback.inv

/-- The original affine cubic chart meets every coefficient fiber. -/
theorem affineChartStructure_surjective : Surjective (chartStructure W 2) := inferInstance

end FLT.Mazur.WeierstrassIntegralChart
