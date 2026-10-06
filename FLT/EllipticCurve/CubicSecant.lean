/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicNegationInvolution
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The secant addition morphism

Addition on the open of the ordinary chart product where the difference
of the x-coordinates is invertible. No smoothness hypothesis is needed here.
This does not yet extend addition across the complementary locus. -/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The secant formula preserves the equation over a ring when its denominator is a unit. -/
theorem equation_secant {x₁ y₁ x₂ y₂ l t : R}
    (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hl : y₂ - y₁ = l * (x₂ - x₁)) (ht : (x₂ - x₁) * t = 1) :
    W.toAffine.Equation (W.toAffine.addX x₁ x₂ l) (W.toAffine.addY x₁ x₂ y₁ l) := by
  apply (Affine.equation_neg ..).mpr
  rw [Affine.equation_iff'] at h₁ h₂ ⊢
  have hy : y₂ = y₁ + l * (x₂ - x₁) := by linear_combination hl
  rw [hy] at h₂
  let z := W.toAffine.addX x₁ x₂ l
  let k := x₂ * z + 2 * l * y₁ - l ^ 2 * x₁ + W.a₁ * y₁ +
    W.a₃ * l - W.a₄ - x₁ ^ 2 - W.a₂ * x₁
  have hk : (x₂ - x₁) * k = 0 := by
    dsimp [k, z, Affine.addX]
    linear_combination h₂ - h₁
  have hk0 : k = 0 := by
    calc
      k = ((x₂ - x₁) * t) * k := by rw [ht, one_mul]
      _ = t * ((x₂ - x₁) * k) := by ring
      _ = 0 := by rw [hk, mul_zero]
  dsimp [k, z, Affine.addX] at hk0
  simp only [Affine.negAddY, Affine.addX]
  linear_combination h₁ + (l ^ 2 + W.a₁ * l - W.a₂ - x₁ - x₂ - x₁) * hk0

/-- Coordinate ring of the product of two ordinary charts over the coefficient base. -/
abbrev AffinePairRing := Ring W false ⊗[R] Ring W false

/-- The difference of x-coordinates on the ordinary chart product. -/
def secantDenominator : AffinePairRing W :=
  (Algebra.TensorProduct.includeRight : Ring W false →ₐ[R] AffinePairRing W)
      (coord W false 0) -
    (Algebra.TensorProduct.includeLeft : Ring W false →ₐ[R] AffinePairRing W)
      (coord W false 0)

/-- Coordinate ring of the open where the secant denominator is invertible. -/
abbrev SecantRing := Localization.Away (secantDenominator W)

/-- The first or second input point of the universal secant. -/
def secantInput (b : Bool) : Ring W false →ₐ[R] SecantRing W :=
  (IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)).comp
    (if b then Algebra.TensorProduct.includeRight else Algebra.TensorProduct.includeLeft)

/-- The ordinary chart product embeds in the full cubic product. -/
def affinePairInclusion :
    pullback (chartToBase W false) (chartToBase W false) ⟶
      pullback (toBase W) (toBase W) :=
  pullback.map _ _ _ _ (affineChart W) (affineChart W) (𝟙 _)
    (by simp) (by simp)

instance affinePairInclusion_isOpenImmersion : IsOpenImmersion (affinePairInclusion W) := by
  unfold affinePairInclusion
  infer_instance

/-- The secant domain is an actual open subscheme of the cubic product. -/
def secantInclusion :
    Spec (.of (SecantRing W)) ⟶ pullback (toBase W) (toBase W) :=
  Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W))) ≫
    (pullbackSpecIso R (Ring W false) (Ring W false)).inv ≫ affinePairInclusion W

instance secantInclusion_isOpenImmersion : IsOpenImmersion (secantInclusion W) := by
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W)))) :=
    IsOpenImmersion.of_isLocalization (secantDenominator W)
  unfold secantInclusion
  infer_instance

@[reassoc (attr := simp)] theorem secantInclusion_fst :
    secantInclusion W ≫ pullback.fst (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom (secantInput W false).toRingHom) ≫ affineChart W := by
  unfold secantInclusion affinePairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_fst, pullbackSpecIso_inv_fst_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

@[reassoc (attr := simp)] theorem secantInclusion_snd :
    secantInclusion W ≫ pullback.snd (toBase W) (toBase W) =
      Spec.map (CommRingCat.ofHom (secantInput W true).toRingHom) ≫ affineChart W := by
  unfold secantInclusion affinePairInclusion chartToBase
  simp only [Category.assoc, pullback.map, pullback.lift_snd, pullbackSpecIso_inv_snd_assoc]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Coordinates of the two universal input points. -/
def secantCoord (b : Bool) (i : Fin 2) : SecantRing W := secantInput W b (coord W false i)

/-- Inverse of the universal secant denominator. -/
def secantInv : SecantRing W := IsLocalization.Away.invSelf (secantDenominator W)

theorem secant_difference_mul_inv :
    (secantCoord W true 0 - secantCoord W false 0) * secantInv W = 1 := by
  let f := IsScalarTower.toAlgHom R (AffinePairRing W) (SecantRing W)
  let x : AffinePairRing W :=
    (Algebra.TensorProduct.includeRight : Ring W false →ₐ[R] AffinePairRing W)
      (coord W false 0)
  let y : AffinePairRing W :=
    (Algebra.TensorProduct.includeLeft : Ring W false →ₐ[R] AffinePairRing W)
      (coord W false 0)
  have h := map_sub f x y
  change f (secantDenominator W) = secantCoord W true 0 - secantCoord W false 0 at h
  rw [← h]
  exact IsLocalization.Away.mul_invSelf (secantDenominator W)

/-- Slope of the universal secant. -/
def secantSlope : SecantRing W :=
  (secantCoord W true 1 - secantCoord W false 1) * secantInv W

theorem secant_slope_relation :
    secantCoord W true 1 - secantCoord W false 1 =
      secantSlope W * (secantCoord W true 0 - secantCoord W false 0) := by
  unfold secantSlope
  rw [mul_assoc, mul_comm (secantInv W), secant_difference_mul_inv, mul_one]

theorem secant_input_equation (b : Bool) :
    (W.map (algebraMap R (SecantRing W))).toAffine.Equation
      (secantCoord W b 0) (secantCoord W b 1) := by
  have h := eval₂_coord_equation W false (secantInput W b).toRingHom
  simpa [equation, Affine.equation_iff', secantCoord, WeierstrassCurve.map,
    AlgHom.comp_algebraMap] using h

/-- Coordinates of the universal secant sum in the ordinary chart. -/
def secantSumCoords : Fin 2 → SecantRing W :=
  let E := (W.map (algebraMap R (SecantRing W))).toAffine
  ![E.addX (secantCoord W false 0) (secantCoord W true 0) (secantSlope W),
    E.addY (secantCoord W false 0) (secantCoord W true 0)
      (secantCoord W false 1) (secantSlope W)]

theorem secantSum_root : aeval (secantSumCoords W) (equation W false) = 0 := by
  have h := equation_secant (W.map (algebraMap R (SecantRing W)))
    (secant_input_equation W false) (secant_input_equation W true)
    (secant_slope_relation W) (secant_difference_mul_inv W)
  simpa [Affine.equation_iff', equation, secantSumCoords, WeierstrassCurve.map] using h

/-- Pullback on functions for addition on the secant open. -/
def secantSum : Ring W false →ₐ[R] SecantRing W :=
  Ideal.Quotient.liftₐ (Ideal.span {equation W false}) (aeval (secantSumCoords W)) (by
    change Ideal.span {equation W false} ≤
      RingHom.ker (aeval (secantSumCoords W) : MvPolynomial (Fin 2) R →ₐ[R] SecantRing W).toRingHom
    rw [Ideal.span_le]
    intro p hp
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact secantSum_root W)

@[simp] theorem secantSum_coord (i : Fin 2) :
    secantSum W (coord W false i) = secantSumCoords W i := by
  change aeval _ (X i) = _
  simp

/-- Addition on the secant open, with values in the glued cubic. -/
def secantAddition : Spec (.of (SecantRing W)) ⟶ scheme W :=
  Spec.map (CommRingCat.ofHom (secantSum W).toRingHom) ≫ affineChart W

/-- The structure map of the secant open. -/
def secantToBase : Spec (.of (SecantRing W)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (SecantRing W)))

@[reassoc (attr := simp)] theorem secantAddition_toBase :
    secantAddition W ≫ toBase W = secantToBase W := by
  unfold secantAddition secantToBase
  rw [Category.assoc, affineChart_toBase]
  unfold chartToBase
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (secantSum W).comp_algebraMap

end WeierstrassCurve.CubicCharts
