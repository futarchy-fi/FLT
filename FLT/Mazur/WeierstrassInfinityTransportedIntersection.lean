/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassInfinityAdditionChart
public import FLT.Mazur.WeierstrassTransportedAdditionRing

/-!
# Infinity and transported affine domains on their full intersection

The tensor ring is the actual fiber product over the Y-chart input product.
No polynomial output coordinate or difference of inputs is inverted, so this
intersection retains the diagonal and the polynomial addition base locus.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (i : AdditionChartIndex)

instance transportedYInputAlgebra :
    Algebra (ChartProduct W 1 1) (TransportedAdditionRing W 1 1 i) :=
  (transportedAdditionInput W 1 1 i).toRingHom.toAlgebra

instance transportedYInputTower :
    IsScalarTower R (ChartProduct W 1 1) (TransportedAdditionRing W 1 1 i) :=
  IsScalarTower.of_algebraMap_eq' (transportedAdditionInput W 1 1 i).comp_algebraMap.symm

/-- The full intersection, including the polynomial base locus. -/
def InfinityTransportedIntersection :=
  TransportedAdditionRing W 1 1 i ⊗[ChartProduct W 1 1] InfinityAdditionOpen W

instance : CommRing (InfinityTransportedIntersection W i) :=
  inferInstanceAs (CommRing (_ ⊗[ChartProduct W 1 1] _))

instance : Algebra R (InfinityTransportedIntersection W i) :=
  inferInstanceAs (Algebra R (_ ⊗[ChartProduct W 1 1] _))

/-- Restriction from the transported affine domain to the full intersection. -/
def infinityTransportedAffine :
    TransportedAdditionRing W 1 1 i →ₐ[R] InfinityTransportedIntersection W i :=
  Algebra.TensorProduct.includeLeft

/-- Restriction from the infinity domain to the full intersection. -/
def infinityTransportedInfinity :
    InfinityAdditionOpen W →ₐ[R] InfinityTransportedIntersection W i :=
  Algebra.TensorProduct.includeRight.restrictScalars R

/-- The two input pairs agree on the full intersection. -/
theorem infinityTransported_inputs :
    (infinityTransportedAffine W i).comp (transportedAdditionInput W 1 1 i) =
      (infinityTransportedInfinity W i).comp (infinityAdditionRestriction W) := by
  apply AlgHom.ext
  intro a
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul
    (R := ChartProduct W 1 1) (A := TransportedAdditionRing W 1 1 i)
    (B := InfinityAdditionOpen W) a

/-- Its spectrum is the actual intersection of the two addition domains. -/
theorem infinityTransported_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (infinityTransportedAffine W i).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityTransportedInfinity W i).toRingHom))
      (Spec.map (CommRingCat.ofHom (transportedAdditionInput W 1 1 i).toRingHom))
      (Spec.map (CommRingCat.ofHom (infinityAdditionRestriction W).toRingHom)) := by
  apply isPullback_SpecMap_of_isPushout
  exact CommRingCat.isPushout_tensorProduct (ChartProduct W 1 1)
    (TransportedAdditionRing W 1 1 i) (InfinityAdditionOpen W)

/-- The original affine addition functions restricted to the full intersection. -/
def infinityTransportedChart :
    additionChartRing W i →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedAffine W i).comp (transportedAdditionAffine W 1 1 i)

/-- The common unnormalized Y-chart inputs. -/
def infinityTransportedInput : ChartProduct W 1 1 →ₐ[R] InfinityTransportedIntersection W i :=
  (infinityTransportedInfinity W i).comp (infinityAdditionRestriction W)

/-- The common input map is also the transported affine input map. -/
theorem infinityTransportedInput_eq :
    infinityTransportedInput W i =
      (infinityTransportedAffine W i).comp (transportedAdditionInput W 1 1 i) :=
  (infinityTransported_inputs W i).symm

end FLT.Mazur.WeierstrassIntegralChart
