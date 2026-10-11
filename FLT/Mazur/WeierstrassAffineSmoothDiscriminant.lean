/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EllipticRationalSingularity
public import FLT.Mazur.WeierstrassAffineRelativeSmoothCriterion
public import FLT.Mazur.WeierstrassAffineMonicComparison
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Smooth affine Weierstrass charts have nonzero discriminant

A zero discriminant produces a singular point over the algebraic closure.
Relative smoothness forbids that point by the existing tangent obstruction.
This proves nonsingularity over an arbitrary original field.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {K : Type u} [Field K] (W : WeierstrassCurve K)

/-- Smoothness of the actual affine chart forces a nonzero original discriminant. -/
theorem discriminant_ne_zero_of_smooth_affineChart [Smooth (chartStructure W 2)] : W.Δ ≠ 0 := by
  intro hd
  let L := AlgebraicClosure K
  have hm : (W.map (algebraMap K L)).Δ = 0 := by rw [map_Δ, hd, map_zero]
  obtain ⟨x, y, he, hn⟩ := exists_singular_of_discriminant_zero (W.map (algebraMap K L)) hm
  let e := evaluation W 2 ![x, y, 1] ((Projective.equation_some x y).mpr he) rfl
  apply hn
  have hs : Set.range (Spec.map (CommRingCat.ofHom e.toRingHom)) ⊆
      (chartStructure W 2).smoothLocus := by
    rw [Scheme.Hom.smoothLocus_eq_top]
    exact Set.subset_univ _
  simpa only [e, evaluation_coord, Matrix.cons_val_zero, Matrix.cons_val_one] using
    affineFieldPoint_nonsingular_of_smooth W e hs

/-- The affine smoothness test constructs the elliptic discriminant condition. -/
theorem isElliptic_of_smooth_affineChart [Smooth (chartStructure W 2)] : W.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (discriminant_ne_zero_of_smooth_affineChart W)⟩

/-- Smoothness of the monic affine coordinate spectrum also detects ellipticity. -/
theorem isElliptic_of_smooth_monic
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing)))] :
    W.IsElliptic := by
  have hs : (algebraMap K W.toAffine.CoordinateRing).Smooth :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)
      (φ := CommRingCat.ofHom (algebraMap K W.toAffine.CoordinateRing))).mp inferInstance
  let _ : Algebra.Smooth K W.toAffine.CoordinateRing := RingHom.smooth_algebraMap.mp hs
  let _ : Algebra.Smooth K (Coordinate W 2) :=
    Algebra.Smooth.of_equiv (affineChartMonicEquiv W).symm
  let _ : Smooth (chartStructure W 2) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr inferInstance)
  exact isElliptic_of_smooth_affineChart W

end FLT.Mazur.WeierstrassIntegralChart
