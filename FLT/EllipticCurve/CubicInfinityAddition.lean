/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicInfinityChord
public import FLT.EllipticCurve.CubicProjectiveLocal

/-! # A local addition morphism near the pair of infinity sections -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Either input map on the product of the infinity charts. -/
def infinityPairInput (b : Bool) : Ring W true →ₐ[R] ChartPairRing W true true :=
  if b then Algebra.TensorProduct.includeRight else Algebra.TensorProduct.includeLeft

/-- Coordinates of either input in the infinity-chart product. -/
def infinityPairCoord (b : Bool) (i : Fin 2) : ChartPairRing W true true :=
  infinityPairInput W b (coord W true i)

/-- Denominator of the divided-difference direction near the pair of infinities. -/
def infinitySlopeDenominator : ChartPairRing W true true :=
  infinityChordDenominator (W.map (algebraMap R (ChartPairRing W true true)))
    (infinityPairCoord W true 0) (infinityPairCoord W false 1) (infinityPairCoord W true 1)

/-- Ring on which the divided-difference direction is defined. -/
abbrev InfinitySlopeRing := Localization.Away (infinitySlopeDenominator W)

/-- Restriction to the direction domain. -/
def infinitySlopeRestriction : ChartPairRing W true true →ₐ[R] InfinitySlopeRing W :=
  IsScalarTower.toAlgHom R (ChartPairRing W true true) (InfinitySlopeRing W)

/-- An input map on the direction domain. -/
def infinitySlopeInput (b : Bool) : Ring W true →ₐ[R] InfinitySlopeRing W :=
  (infinitySlopeRestriction W).comp (infinityPairInput W b)

/-- Input coordinates on the direction domain. -/
def infinitySlopeCoord (b : Bool) (i : Fin 2) : InfinitySlopeRing W :=
  infinitySlopeInput W b (coord W true i)

/-- The inverse of the direction denominator. -/
def infinitySlopeInv : InfinitySlopeRing W :=
  IsLocalization.Away.invSelf (infinitySlopeDenominator W)

theorem infinityChordDenominator_baseChange {A B : Type*} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (r v w : A) :
    f (infinityChordDenominator (W.map (algebraMap R A)) r v w) =
      infinityChordDenominator (W.map (algebraMap R B)) (f r) (f v) (f w) := by
  simp [infinityChordDenominator, WeierstrassCurve.map]

theorem infinitySlope_denominator_mul_inv :
    infinityChordDenominator (W.map (algebraMap R (InfinitySlopeRing W)))
      (infinitySlopeCoord W true 0) (infinitySlopeCoord W false 1)
      (infinitySlopeCoord W true 1) * infinitySlopeInv W = 1 := by
  have h := infinityChordDenominator_baseChange W (infinitySlopeRestriction W)
    (infinityPairCoord W true 0) (infinityPairCoord W false 1) (infinityPairCoord W true 1)
  change infinitySlopeRestriction W (infinitySlopeDenominator W) =
    infinityChordDenominator (W.map (algebraMap R (InfinitySlopeRing W)))
      (infinitySlopeCoord W true 0) (infinitySlopeCoord W false 1)
      (infinitySlopeCoord W true 1) at h
  rw [← h]
  exact IsLocalization.Away.mul_invSelf (infinitySlopeDenominator W)

theorem infinitySlope_input_equation (b : Bool) :
    (W.map (algebraMap R (InfinitySlopeRing W))).toProjective.Equation
      ![infinitySlopeCoord W b 0, 1, infinitySlopeCoord W b 1] :=
  chartPointCoords_equation W true (infinitySlopeInput W b)

/-- Direction of a chord or tangent expressed as a change in Z per unit change in X. -/
def infinitySlope : InfinitySlopeRing W :=
  infinityChordNumerator (W.map (algebraMap R (InfinitySlopeRing W)))
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0)
    (infinitySlopeCoord W false 1) * infinitySlopeInv W

theorem infinitySlope_normal :
    infinitySlope W * infinityChordDenominator (W.map (algebraMap R (InfinitySlopeRing W)))
      (infinitySlopeCoord W true 0) (infinitySlopeCoord W false 1)
      (infinitySlopeCoord W true 1) =
    infinityChordNumerator (W.map (algebraMap R (InfinitySlopeRing W)))
      (infinitySlopeCoord W false 0) (infinitySlopeCoord W true 0)
      (infinitySlopeCoord W false 1) := by
  unfold infinitySlope
  rw [mul_assoc, mul_comm (infinitySlopeInv W), infinitySlope_denominator_mul_inv, mul_one]

theorem infinitySlope_relation :
    infinitySlopeCoord W true 1 - infinitySlopeCoord W false 1 =
      infinitySlope W * (infinitySlopeCoord W true 0 - infinitySlopeCoord W false 0) := by
  have h := infinity_chord_relation (W.map (algebraMap R (InfinitySlopeRing W)))
    (infinitySlope_input_equation W false) (infinitySlope_input_equation W true)
  have h' := congrArg (fun x ↦ x * infinitySlopeInv W) h
  rw [mul_assoc, infinitySlope_denominator_mul_inv, mul_one] at h'
  unfold infinitySlope
  linear_combination h'

/-- Homogeneous addition coordinates on the direction domain. -/
def infinitySumProjective : Fin 3 → InfinitySlopeRing W :=
  infinityChord (W.map (algebraMap R (InfinitySlopeRing W)))
    (infinitySlopeCoord W false 0) (infinitySlopeCoord W false 1)
    (infinitySlopeCoord W true 0) (infinitySlope W)

theorem infinitySumProjective_equation :
    (W.map (algebraMap R (InfinitySlopeRing W))).toProjective.Equation
      (infinitySumProjective W) :=
  infinityChord_equation _ (infinitySlope_input_equation W false)
    (infinitySlope_relation W) (infinitySlope_normal W)

/-- A neighborhood of the pair of infinity sections where the sum lies in the infinity chart. -/
abbrev InfinityAdditionRing := Localization.Away (infinitySumProjective W 1)

/-- Restriction from the direction domain to the normalized sum domain. -/
def infinityAdditionRestriction : InfinitySlopeRing W →ₐ[R] InfinityAdditionRing W :=
  IsScalarTower.toAlgHom R _ _

/-- Inverse of the homogeneous Y-coordinate of the sum. -/
def infinityAdditionInv : InfinityAdditionRing W :=
  IsLocalization.Away.invSelf (infinitySumProjective W 1)

/-- Coordinates of the sum in the infinity chart. -/
def infinityAdditionCoords : Fin 2 → InfinityAdditionRing W :=
  ![infinityAdditionRestriction W (infinitySumProjective W 0) * infinityAdditionInv W,
    infinityAdditionRestriction W (infinitySumProjective W 2) * infinityAdditionInv W]

theorem infinityAdditionCoords_root :
    aeval (infinityAdditionCoords W) (equation W true) = 0 := by
  have hp := infinitySumProjective_equation W
  have he : infinitySumProjective W =
      ![infinitySumProjective W 0, infinitySumProjective W 1, infinitySumProjective W 2] := by
    ext i
    fin_cases i <;> rfl
  rw [he] at hp
  exact infinity_normalize_algHom W (infinityAdditionRestriction W) hp
    (IsLocalization.Away.mul_invSelf
      (S := InfinityAdditionRing W) (infinitySumProjective W 1))

/-- Pullback of functions for addition near the pair of infinity sections. -/
def infinityAdditionSum : Ring W true →ₐ[R] InfinityAdditionRing W :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W true}) (aeval (infinityAdditionCoords W)) (by
    change Ideal.span {equation W true} ≤
      RingHom.ker (aeval (infinityAdditionCoords W) :
        MvPolynomial (Fin 2) R →ₐ[R] InfinityAdditionRing W).toRingHom
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact infinityAdditionCoords_root W)

@[simp] theorem infinityAdditionSum_coord (i : Fin 2) :
    infinityAdditionSum W (coord W true i) = infinityAdditionCoords W i := by
  change aeval _ (X i) = _
  simp

/-- The infinity addition domain embeds as an open of the full cubic product. -/
def infinityAdditionInclusion :
    Spec (.of (InfinityAdditionRing W)) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinitySlopeRing W) (InfinityAdditionRing W))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (ChartPairRing W true true) (InfinitySlopeRing W))) ≫
      (pullbackSpecIso R (Ring W true) (Ring W true)).inv ≫ chartPairInclusion W true true

instance infinityAdditionInclusion_isOpenImmersion :
    IsOpenImmersion (infinityAdditionInclusion W) := by
  have : IsOpenImmersion (Spec.map
      (CommRingCat.ofHom (algebraMap (InfinitySlopeRing W) (InfinityAdditionRing W)))) :=
    IsOpenImmersion.of_isLocalization (infinitySumProjective W 1)
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (ChartPairRing W true true) (InfinitySlopeRing W)))) :=
    IsOpenImmersion.of_isLocalization (infinitySlopeDenominator W)
  unfold infinityAdditionInclusion
  infer_instance

/-- Addition on a neighborhood of infinity plus infinity. -/
def infinityAddition : Spec (.of (InfinityAdditionRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (infinityAdditionSum W).toRingHom) ≫ infinityChart W

@[reassoc (attr := simp)] theorem infinityAddition_toBase :
    infinityAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (InfinityAdditionRing W))) := by
  unfold infinityAddition
  rw [Category.assoc, infinityChart_toBase]
  unfold chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (infinityAdditionSum W).comp_algebraMap

end WeierstrassCurve.CubicCharts
