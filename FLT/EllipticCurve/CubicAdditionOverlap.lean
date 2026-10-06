/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicTangent

/-! # Agreement of secant and tangent addition -/

@[expose] public noncomputable section
open scoped TensorProduct
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
set_option backward.isDefEq.respectTransparency false

namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Coordinate ring of the scheme-theoretic intersection of the two opens. -/
abbrev SecantTangentRing :=
  SecantRing W ⊗[AffinePairRing W] TangentRing W

/-- Restriction from the secant domain to the intersection. -/
def secantRestriction : SecantRing W →ₐ[R] SecantTangentRing W :=
  (Algebra.TensorProduct.includeLeft :
    SecantRing W →ₐ[AffinePairRing W] SecantTangentRing W).restrictScalars R

/-- Restriction from the tangent domain to the intersection. -/
def tangentRestriction : TangentRing W →ₐ[R] SecantTangentRing W :=
  (Algebra.TensorProduct.includeRight :
    TangentRing W →ₐ[AffinePairRing W] SecantTangentRing W).restrictScalars R

theorem secant_tangent_coord (b : Bool) (i : Fin 2) :
    secantRestriction W (secantCoord W b i) =
      tangentRestriction W (tangentCoord W b i) := by
  have h₁ := (Algebra.TensorProduct.includeLeft :
    SecantRing W →ₐ[AffinePairRing W] SecantTangentRing W).commutes (pairCoord W b i)
  have h₂ := (Algebra.TensorProduct.includeRight :
    TangentRing W →ₐ[AffinePairRing W] SecantTangentRing W).commutes (pairCoord W b i)
  exact h₁.trans h₂.symm

/-- Both constructions choose the same slope on their intersection. -/
theorem secant_tangent_slope :
    secantRestriction W (secantSlope W) = tangentRestriction W (tangentSlope W) := by
  have hs := congrArg (secantRestriction W) (secant_slope_relation W)
  have ht := congrArg (tangentRestriction W) (tangent_slope_relation W)
  have hi := congrArg (secantRestriction W) (secant_difference_mul_inv W)
  simp only [map_sub, map_mul, secant_tangent_coord] at hs ht
  simp only [map_sub, map_mul, map_one, secant_tangent_coord] at hi
  let d := tangentRestriction W (tangentCoord W true 0) -
    tangentRestriction W (tangentCoord W false 0)
  let v := secantRestriction W (secantInv W)
  have hd : d * v = 1 := hi
  have he : (secantRestriction W (secantSlope W) -
      tangentRestriction W (tangentSlope W)) * d = 0 := by
    dsimp [d]
    linear_combination ht - hs
  have hzero : secantRestriction W (secantSlope W) -
      tangentRestriction W (tangentSlope W) = 0 := by
    calc
      _ = (secantRestriction W (secantSlope W) -
          tangentRestriction W (tangentSlope W)) * (d * v) := by rw [hd, mul_one]
      _ = 0 := by rw [← mul_assoc, he, zero_mul]
  exact sub_eq_zero.mp hzero

/-- Equality as algebra maps, not merely equality on field-valued points. -/
theorem secant_tangent_sum :
    (secantRestriction W).comp (secantSum W) =
      (tangentRestriction W).comp (tangentSum W) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change secantRestriction W (secantSum W (coord W false i)) =
    tangentRestriction W (tangentSum W (coord W false i))
  rw [secantSum_coord, tangentSum_coord]
  fin_cases i <;>
    simp [secantSumCoords, tangentSumCoords, Affine.addY, Affine.negAddY, Affine.negY,
      secant_tangent_coord, secant_tangent_slope, WeierstrassCurve.map]

/-- The two scheme morphisms agree on the common open. -/
theorem secant_tangent_agreement :
    Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫ secantAddition W =
      Spec.map (CommRingCat.ofHom (tangentRestriction W).toRingHom) ≫ tangentAddition W := by
  unfold secantAddition tangentAddition
  rw [← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  congr 1
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact DFunLike.congr_fun (secant_tangent_sum W) x

/-- The tensor product represents the intersection of the two affine opens. -/
theorem secant_tangent_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom))
      (Spec.map (CommRingCat.ofHom (tangentRestriction W).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (SecantRing W))))
      (Spec.map (CommRingCat.ofHom (algebraMap (AffinePairRing W) (TangentRing W)))) := by
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct (AffinePairRing W) (SecantRing W) (TangentRing W))

end WeierstrassCurve.CubicCharts
