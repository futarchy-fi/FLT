/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicSecant

/-! # Addition near the nonvertical part of the diagonal

The divided difference of the Weierstrass equation supplies a slope even when
the two x-coordinates coincide. This extends the secant construction over the
open where the sum of the y-coordinates plus a₁*x₂+a₃ is invertible. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Denominator of the alternative secant slope, including nonvertical tangents. -/
def chordDenominator (x₂ y₁ y₂ : R) : R := y₂ + y₁ + W.a₁ * x₂ + W.a₃

/-- Divided difference of the cubic in x, corrected by the mixed term. -/
def chordNumerator (x₁ x₂ y₁ : R) : R :=
  x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2 + W.a₂ * (x₁ + x₂) + W.a₄ - W.a₁ * y₁

theorem chord_relation {x₁ y₁ x₂ y₂ : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂) :
    (y₂ - y₁) * chordDenominator W x₂ y₁ y₂ =
      (x₂ - x₁) * chordNumerator W x₁ x₂ y₁ := by
  rw [Affine.equation_iff'] at h₁ h₂
  unfold chordDenominator chordNumerator
  linear_combination h₂ - h₁

/-- Two polynomial slope identities suffice, without canceling an x-difference. -/
theorem equation_chord {x₁ y₁ x₂ y₂ l : R}
    (h₁ : W.toAffine.Equation x₁ y₁)
    (hl : y₂ - y₁ = l * (x₂ - x₁))
    (hn : l * chordDenominator W x₂ y₁ y₂ = chordNumerator W x₁ x₂ y₁) :
    W.toAffine.Equation (W.toAffine.addX x₁ x₂ l) (W.toAffine.addY x₁ x₂ y₁ l) := by
  apply (Affine.equation_neg ..).mpr
  rw [Affine.equation_iff'] at h₁ ⊢
  let z := W.toAffine.addX x₁ x₂ l
  let k := x₂ * z + 2 * l * y₁ - l ^ 2 * x₁ + W.a₁ * y₁ +
    W.a₃ * l - W.a₄ - x₁ ^ 2 - W.a₂ * x₁
  have hk : k = 0 := by
    dsimp [k, z, Affine.addX]
    unfold chordDenominator chordNumerator at hn
    linear_combination hn - l * hl
  dsimp [k, z, Affine.addX] at hk
  simp only [Affine.negAddY, Affine.addX]
  linear_combination h₁ + (l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂ - x₁) * hk

/-- The two coordinate-ring maps into the affine product. -/
def pairInput (b : Bool) : Ring W false →ₐ[R] AffinePairRing W :=
  if b then Algebra.TensorProduct.includeRight else Algebra.TensorProduct.includeLeft

/-- Coordinates of either input on the affine chart product. -/
def pairCoord (b : Bool) (i : Fin 2) : AffinePairRing W := pairInput W b (coord W false i)

/-- The nonvertical tangent denominator on the ordinary chart product. -/
def tangentDenominator : AffinePairRing W :=
  chordDenominator (W.map (algebraMap R (AffinePairRing W)))
    (pairCoord W true 0) (pairCoord W false 1) (pairCoord W true 1)

/-- Coordinate ring of the nonvertical tangent open. -/
abbrev TangentRing := Localization.Away (tangentDenominator W)

/-- Pullback of either input chart to the tangent open. -/
def tangentInput (b : Bool) : Ring W false →ₐ[R] TangentRing W :=
  (IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)).comp (pairInput W b)

/-- Input coordinates restricted to the tangent open. -/
def tangentCoord (b : Bool) (i : Fin 2) : TangentRing W := tangentInput W b (coord W false i)

/-- Inverse of the divided-difference denominator. -/
def tangentInv : TangentRing W := IsLocalization.Away.invSelf (tangentDenominator W)

theorem tangent_denominator_mul_inv :
    chordDenominator (W.map (algebraMap R (TangentRing W)))
      (tangentCoord W true 0) (tangentCoord W false 1) (tangentCoord W true 1) *
        tangentInv W = 1 := by
  let f := IsScalarTower.toAlgHom R (AffinePairRing W) (TangentRing W)
  have h : f (tangentDenominator W) =
      chordDenominator (W.map (algebraMap R (TangentRing W)))
        (tangentCoord W true 0) (tangentCoord W false 1) (tangentCoord W true 1) := by
    simp only [tangentDenominator, chordDenominator, WeierstrassCurve.map,
      map_add, map_mul, AlgHom.commutes]
    rfl
  rw [← h]
  exact IsLocalization.Away.mul_invSelf (tangentDenominator W)

theorem tangent_input_equation (b : Bool) :
    (W.map (algebraMap R (TangentRing W))).toAffine.Equation
      (tangentCoord W b 0) (tangentCoord W b 1) := by
  have h := eval₂_coord_equation W false (tangentInput W b).toRingHom
  simpa [equation, Affine.equation_iff', tangentCoord, WeierstrassCurve.map,
    AlgHom.comp_algebraMap] using h

/-- The divided-difference slope on its domain of definition. -/
def tangentSlope : TangentRing W :=
  chordNumerator (W.map (algebraMap R (TangentRing W)))
    (tangentCoord W false 0) (tangentCoord W true 0) (tangentCoord W false 1) * tangentInv W

theorem tangent_slope_normal :
    tangentSlope W * chordDenominator (W.map (algebraMap R (TangentRing W)))
      (tangentCoord W true 0) (tangentCoord W false 1) (tangentCoord W true 1) =
    chordNumerator (W.map (algebraMap R (TangentRing W)))
      (tangentCoord W false 0) (tangentCoord W true 0) (tangentCoord W false 1) := by
  unfold tangentSlope
  rw [mul_assoc, mul_comm (tangentInv W), tangent_denominator_mul_inv, mul_one]

theorem tangent_slope_relation :
    tangentCoord W true 1 - tangentCoord W false 1 =
      tangentSlope W * (tangentCoord W true 0 - tangentCoord W false 0) := by
  have h := chord_relation (W.map (algebraMap R (TangentRing W)))
    (tangent_input_equation W false) (tangent_input_equation W true)
  have h' := congrArg (fun x ↦ x * tangentInv W) h
  rw [mul_assoc, tangent_denominator_mul_inv, mul_one] at h'
  unfold tangentSlope
  linear_combination h'

/-- Affine coordinates of the sum on the tangent open. -/
def tangentSumCoords : Fin 2 → TangentRing W :=
  let E := (W.map (algebraMap R (TangentRing W))).toAffine
  ![E.addX (tangentCoord W false 0) (tangentCoord W true 0) (tangentSlope W),
    E.addY (tangentCoord W false 0) (tangentCoord W true 0)
      (tangentCoord W false 1) (tangentSlope W)]

theorem tangentSum_root : aeval (tangentSumCoords W) (equation W false) = 0 := by
  have h := equation_chord (W.map (algebraMap R (TangentRing W)))
    (tangent_input_equation W false) (tangent_slope_relation W) (tangent_slope_normal W)
  simpa [Affine.equation_iff', equation, tangentSumCoords, WeierstrassCurve.map] using h

/-- Pullback of functions along addition on the tangent open. -/
def tangentSum : Ring W false →ₐ[R] TangentRing W :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W false}) (aeval (tangentSumCoords W)) (by
    change Ideal.span {equation W false} ≤
      RingHom.ker (aeval (tangentSumCoords W) :
        MvPolynomial (Fin 2) R →ₐ[R] TangentRing W).toRingHom
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact tangentSum_root W)

@[simp] theorem tangentSum_coord (i : Fin 2) :
    tangentSum W (coord W false i) = tangentSumCoords W i := by
  change aeval _ (X i) = _
  simp

/-- The tangent domain is an open of the actual cubic product. -/
def tangentInclusion :
    Spec (.of (TangentRing W)) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (TangentRing W))) ≫
    (pullbackSpecIso R (Ring W false) (Ring W false)).inv ≫ affinePairInclusion W

instance tangentInclusion_isOpenImmersion : IsOpenImmersion (tangentInclusion W) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (TangentRing W)))) :=
    IsOpenImmersion.of_isLocalization (tangentDenominator W)
  unfold tangentInclusion
  infer_instance

@[reassoc (attr := simp)] theorem tangentInclusion_fst :
    tangentInclusion W ≫ pullback.fst (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom (tangentInput W false).toRingHom) ≫ affineChart W := by
  unfold tangentInclusion affinePairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)] theorem tangentInclusion_snd :
    tangentInclusion W ≫ pullback.snd (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom (tangentInput W true).toRingHom) ≫ affineChart W := by
  unfold tangentInclusion affinePairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Addition on the nonvertical tangent open. -/
def tangentAddition : Spec (.of (TangentRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (tangentSum W).toRingHom) ≫ affineChart W

@[reassoc (attr := simp)] theorem tangentAddition_toBase :
    tangentAddition W ≫ toBase W =
      Spec.map (CommRingCat.ofHom (algebraMap R (TangentRing W))) := by
  unfold tangentAddition
  rw [Category.assoc, affineChart_toBase]
  unfold chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (tangentSum W).comp_algebraMap

end WeierstrassCurve.CubicCharts
