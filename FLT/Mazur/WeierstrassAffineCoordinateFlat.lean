/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineMonicComparison
public import FLT.Mazur.WeierstrassFlatSectionRegular
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-!
# Flatness over the affine X line and regular coordinate differences

The explicit monic comparison makes the actual affine chart flat over R[X].
Consequently X minus any coefficient is regular, including after arbitrary
flat extensions. This supplies the affine regularity needed for the input minor.
-/

@[expose] public noncomputable section

open Polynomial

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The original affine quotient is free over its coefficient ring. -/
theorem affineChart_free : Module.Free R (Coordinate W 2) :=
  Module.Free.of_equiv (affineChartMonicEquiv W).symm.toLinearEquiv

/-- The original affine chart is flat over the coefficient ring. -/
theorem affineChart_flat : Module.Flat R (Coordinate W 2) := by
  let _ := affineChart_free W
  infer_instance

/-- The X-coordinate map factors through the monic model's polynomial coefficient map. -/
theorem affineChart_x_factor :
    (aeval (R := R) (coord W 2 0)).toRingHom =
      (affineMonicToChart W).toRingHom.comp
        (algebraMap R[X] W.toAffine.CoordinateRing) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [affineMonicToChart, AdjoinRoot.algebraMap_eq]
  · simp [affineMonicToChart, AdjoinRoot.algebraMap_eq]

/-- The actual affine X-coordinate projection is flat over the polynomial line. -/
theorem affineChart_x_flat : (aeval (R := R) (coord W 2 0)).toRingHom.Flat := by
  rw [affineChart_x_factor]
  apply (RingHom.flat_algebraMap_iff.mpr
    (inferInstance : Module.Flat R[X] W.toAffine.CoordinateRing)).comp
  exact RingHom.Flat.of_bijective (affineChartMonicEquiv W).symm.bijective

/-- Subtracting any base coefficient from the actual X coordinate gives a regular element. -/
theorem affineChart_x_sub_regular (r : R) :
    IsRegular (coord W 2 0 - algebraMap R (Coordinate W 2) r) := by
  have h := flatRingHom_isRegular (aeval (R := R) (coord W 2 0)).toRingHom (affineChart_x_flat W)
    (monic_X_sub_C r).isRegular
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, map_sub, aeval_X, aeval_C] using h

/-- Flat chart extensions retain regularity of the affine X difference. -/
theorem affineChart_x_sub_regular_map {S : Type*} [CommRing S]
    (f : Coordinate W 2 →+* S) (hf : f.Flat) (r : R) :
    IsRegular (f (coord W 2 0) - f (algebraMap R (Coordinate W 2) r)) := by
  simpa only [map_sub] using flatRingHom_isRegular f hf (affineChart_x_sub_regular W r)

end FLT.Mazur.WeierstrassIntegralChart
