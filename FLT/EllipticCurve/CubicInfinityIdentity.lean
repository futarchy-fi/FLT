/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityAddition
public import FLT.EllipticCurve.CubicProjectiveIdentity

/-! # Infinity plus infinity belongs to the local addition domain -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluation at the pair of infinity sections. -/
def infinityPairOrigin : ChartPairRing W true true →ₐ[R] R :=
  Algebra.TensorProduct.productMap (InfinityChart.origin W) (InfinityChart.origin W)

theorem infinityPairOrigin_input (b : Bool) :
    (infinityPairOrigin W).comp (infinityPairInput W b) = InfinityChart.origin W := by
  cases b
  · exact Algebra.TensorProduct.productMap_left _ _
  · exact Algebra.TensorProduct.productMap_right _ _

@[simp] theorem infinityPairOrigin_coord (b : Bool) (i : Fin 2) :
    infinityPairOrigin W (infinityPairCoord W b i) = 0 :=
  (DFunLike.congr_fun (infinityPairOrigin_input W b) (coord W true i)).trans
    (infinity_origin_coord W i)

@[simp] theorem infinityPairOrigin_denominator :
    infinityPairOrigin W (infinitySlopeDenominator W) = 1 := by
  have h := infinityChordDenominator_baseChange W (infinityPairOrigin W)
    (infinityPairCoord W true 0) (infinityPairCoord W false 1) (infinityPairCoord W true 1)
  simp only [infinityPairOrigin_coord] at h
  exact h.trans (by simp [infinityChordDenominator])

/-- The pair of infinity sections factors through the direction domain. -/
def infinitySlopeOrigin : InfinitySlopeRing W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinitySlopeDenominator W)
    (f := infinityPairOrigin W) (by rw [infinityPairOrigin_denominator]; exact isUnit_one)

theorem infinitySlopeOrigin_restriction (x : ChartPairRing W true true) :
    infinitySlopeOrigin W (infinitySlopeRestriction W x) = infinityPairOrigin W x := by
  simp [infinitySlopeOrigin, infinitySlopeRestriction, IsLocalization.Away.liftAlgHom_apply]

@[simp] theorem infinitySlopeOrigin_coord (b : Bool) (i : Fin 2) :
    infinitySlopeOrigin W (infinitySlopeCoord W b i) = 0 :=
  (infinitySlopeOrigin_restriction W (infinityPairCoord W b i)).trans
    (infinityPairOrigin_coord W b i)

@[simp] theorem infinitySlopeOrigin_slope :
    infinitySlopeOrigin W (infinitySlope W) = 0 := by
  have h := infinityChordNumerator_baseChange W (infinitySlopeOrigin W)
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0) (infinitySlopeCoord W false 1)
  simp only [infinitySlopeOrigin_coord] at h
  have hz : infinitySlopeOrigin W
      (infinityChordNumerator (W.map (algebraMap R (InfinitySlopeRing W)))
        (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0)
        (infinitySlopeCoord W false 1)) = 0 :=
    h.trans (by simp [infinityChordNumerator])
  unfold infinitySlope
  rw [map_mul, hz, zero_mul]

theorem infinitySlopeOrigin_sum :
    infinitySlopeOrigin W ∘ infinitySumProjective W = ![0, 1, 0] := by
  have h := infinityChord_baseChange W (infinitySlopeOrigin W)
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W false 1)
    (infinitySlopeCoord W true 0) (infinitySlope W)
  simp only [infinitySlopeOrigin_coord, infinitySlopeOrigin_slope, infinityChord_origin] at h
  exact h

@[simp] theorem infinitySlopeOrigin_denominator :
    infinitySlopeOrigin W (infinitySumProjective W 1) = 1 :=
  congrFun (infinitySlopeOrigin_sum W) 1

/-- The pair of infinity sections factors through the normalized addition domain. -/
def infinityAdditionOrigin : InfinityAdditionRing W →ₐ[R] R :=
  IsLocalization.Away.liftAlgHom (infinitySumProjective W 1)
    (f := infinitySlopeOrigin W) (by rw [infinitySlopeOrigin_denominator]; exact isUnit_one)

theorem infinityAdditionOrigin_restriction (x : InfinitySlopeRing W) :
    infinityAdditionOrigin W (infinityAdditionRestriction W x) = infinitySlopeOrigin W x := by
  simp [infinityAdditionOrigin, infinityAdditionRestriction, IsLocalization.Away.liftAlgHom_apply]

theorem infinityAdditionOrigin_sum :
    (infinityAdditionOrigin W).comp (infinityAdditionSum W) = InfinityChart.origin W := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change infinityAdditionOrigin W (infinityAdditionSum W (coord W true i)) =
    InfinityChart.origin W (coord W true i)
  rw [infinityAdditionSum_coord]
  have hz : ∀ j : Fin 3, j ≠ 1 →
      infinitySlopeOrigin W (infinitySumProjective W j) = 0 := by
    intro j hj
    have h := congrFun (infinitySlopeOrigin_sum W) j
    fin_cases j <;> simp_all
  fin_cases i
  · change infinityAdditionOrigin W (infinityAdditionRestriction W
      (infinitySumProjective W 0) * infinityAdditionInv W) = _
    rw [map_mul, infinityAdditionOrigin_restriction, hz 0 (by decide), zero_mul]
    exact (infinity_origin_coord W 0).symm
  · change infinityAdditionOrigin W (infinityAdditionRestriction W
      (infinitySumProjective W 2) * infinityAdditionInv W) = _
    rw [map_mul, infinityAdditionOrigin_restriction, hz 2 (by decide), zero_mul]
    exact (infinity_origin_coord W 1).symm

/-- The pair of infinity sections, lifted into the local addition domain. -/
def infinityAdditionSection : Spec (.of R) ⟶ Spec (.of (InfinityAdditionRing W)) :=
  Spec.map (CommRingCat.ofHom (infinityAdditionOrigin W).toRingHom)

@[reassoc (attr := simp)] theorem infinityAdditionSection_addition :
    infinityAdditionSection W ≫ infinityAddition W = infinity W := by
  unfold infinityAdditionSection infinityAddition infinity InfinityChart.infinity
  rw [← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom (infinityAdditionOrigin_sum W)

end WeierstrassCurve.CubicCharts
