/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassAffineSmoothDiscriminant
public import FLT.Mazur.WeierstrassChartBaseChangeSquare
public import Mathlib.RingTheory.Ideal.Nonunits

/-!
# A smooth affine Weierstrass chart has invertible discriminant

Apply the field obstruction to every maximal residue field. This detects a
unit in the original coefficient ring, including nonreduced bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- A smooth normalized affine chart has unit discriminant over any coefficient ring. -/
theorem isElliptic_of_relative_smooth_affineChart [Smooth (chartStructure W 2)] :
    W.IsElliptic := by
  constructor
  by_contra hu
  obtain ⟨m, hm, hd⟩ := exists_max_ideal_of_mem_nonunits hu
  let _ : m.IsMaximal := hm
  let _ : Field (R ⧸ m) := Ideal.Quotient.field m
  let _ : Smooth (chartStructure (W.map (algebraMap R (R ⧸ m))) 2) :=
    MorphismProperty.of_isPullback (chartCoefficient_isPullback (S := R ⧸ m) W 2)
      (inferInstance : Smooth (chartStructure W 2))
  have hn := discriminant_ne_zero_of_smooth_affineChart (W.map (algebraMap R (R ⧸ m)))
  apply hn
  rw [map_Δ]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hd

/-- Smoothness of the actual monic spectrum detects ellipticity over arbitrary rings. -/
theorem isElliptic_of_relative_smooth_monic
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)))] :
    W.IsElliptic := by
  have hs : (algebraMap R W.toAffine.CoordinateRing).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing))).mp inferInstance
  let _ : Algebra.Smooth R W.toAffine.CoordinateRing := RingHom.smooth_algebraMap.mp hs
  let _ : Algebra.Smooth R (Coordinate W 2) :=
    Algebra.Smooth.of_equiv (affineChartMonicEquiv W).symm
  let _ : Smooth (chartStructure W 2) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact isElliptic_of_relative_smooth_affineChart W

end FLT.Mazur.WeierstrassIntegralChart
