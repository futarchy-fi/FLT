/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityMonicEquivalence
public import FLT.Mazur.WeierstrassIntegralCurveProduct
public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# Flat projections of the actual infinity product chart

The monic presentation proves flatness over an arbitrary coefficient ring.
Tensor base change then proves flatness of both actual input projections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- The infinity chart is flat over the coefficient spectrum. -/
instance infinityChartStructure_flat : Flat (chartStructure W 1) := by
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr (infinityChart_flat W)

/-- The left inclusion into the tensor product is a flat ring homomorphism. -/
theorem infinityProductLeft_flat : (chartProductLeft W 1 1).toRingHom.Flat := by
  let _ := infinityChart_flat W
  change (algebraMap (Coordinate W 1) (Coordinate W 1 ⊗[R] Coordinate W 1)).Flat
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The right inclusion is flat by interchange of the tensor factors. -/
theorem infinityProductRight_flat : (chartProductRight W 1 1).toRingHom.Flat := by
  let e : ChartProduct W 1 1 ≃+* ChartProduct W 1 1 :=
    (Algebra.TensorProduct.comm R (Coordinate W 1) (Coordinate W 1)).toRingEquiv
  have he : e.toRingHom.Flat := RingHom.Flat.of_bijective e.bijective
  exact (infinityProductLeft_flat W).comp he

/-- First projection of the actual infinity product spectrum is flat. -/
instance infinityProductLeftSpec_flat :
    Flat (Spec.map (CommRingCat.ofHom (chartProductLeft W 1 1).toRingHom)) :=
  Flat.SpecMap_iff.mpr (infinityProductLeft_flat W)

/-- Second projection of the actual infinity product spectrum is flat. -/
instance infinityProductRightSpec_flat :
    Flat (Spec.map (CommRingCat.ofHom (chartProductRight W 1 1).toRingHom)) :=
  Flat.SpecMap_iff.mpr (infinityProductRight_flat W)

/-- The tensor product chart itself is flat over the coefficient spectrum. -/
instance infinityProductStructure_flat :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap R (ChartProduct W 1 1)))) := by
  have h := (RingHom.flat_algebraMap_iff.mpr (infinityChart_flat W)).comp
    (infinityProductLeft_flat W)
  apply Flat.SpecMap_iff.mpr
  convert h using 1
  ext r
  exact ((chartProductLeft W 1 1).commutes r).symm

end FLT.Mazur.WeierstrassIntegralChart
