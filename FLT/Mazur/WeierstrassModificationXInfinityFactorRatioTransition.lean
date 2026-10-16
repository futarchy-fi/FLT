/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInfinityIncidenceTransition
public import FLT.Mazur.WeierstrassInfinityFactorRatioParameter
public import FLT.Mazur.WeierstrassModificationXPolynomialFactors

/-!
# The full infinity factor ratio retains the original projective transition

The two regular numerators pull back to the original tangent factors times
the same invertible X/Y. Their ratio therefore has exactly the original full
factor-ratio denominator on the unchanged original y-localization.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
open WeierstrassIntegralChart
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
  (I : Ideal R) (hI : IsNilpotent I)
  (h2I : W.a₂ ∈ I) (h3I : W.a₃ ∈ I) (h4I : W.a₄ ∈ I) (h6I : W.a₆ ∈ I)
  (r : R[X])
local notation "A" => Coordinate W s b3 b4 b6
local notation "Y" => Localization.Away (y W s b3 b4 b6)
local notation "B" => WeierstrassIntegralChart.Coordinate W 1
local notation "g" => algebraMap A Y
local notation "F" => initialInfinityTransition W s b3 b4 b6 h3 h4 h6
local notation "u" => coord W 1 0
local notation "t∞" => nilpotentInfinityIncidence W I hI h2I h3I h4I h6I s
local notation "V" => polynomialSmallFactor W s b3 b4 b6 r
local notation "U" => polynomialOppositeFactor W s b3 b4 b6 r

/-- Every coefficient of the original polynomial root follows the actual projective transition. -/
theorem initialInfinityTransition_root :
    F (r.eval₂ (algebraMap R B) t∞) = g (algebraMap R[X] A r) := by
  have he : (F).comp (aeval t∞) =
      (IsScalarTower.toAlgHom R A Y).comp (IsScalarTower.toAlgHom R R[X] A) := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, aeval_X]
    change F t∞ = g (t W s b3 b4 b6)
    exact initialInfinityTransition_incidence W s b3 b4 b6 h3 h4 h6 I hI h2I h3I h4I h6I
  exact congrArg (fun f : R[X] →ₐ[R] Y => f r) he

/-- Clearing the small tangent pole agrees with the original full projective transition. -/
theorem initialInfinityTransition_smallFactor :
    F (infinitySmallFactor W I hI h2I h3I h4I h6I s r) = F u * g V := by
  rw [infinitySmallFactor, map_sub, map_one, map_mul, initialInfinityTransition_root,
    polynomialSmallFactor, map_sub]
  have hv := initialInfinityTransition_x_mul_v W s b3 b4 b6 h3 h4 h6
  linear_combination -hv

/-- Clearing the opposite pole retains every original polynomial correction. -/
theorem initialInfinityTransition_oppositeFactor :
    F (infinityOppositeFactor W I hI h2I h3I h4I h6I s b3 r) = F u * g U := by
  have hc (a : R) : g (algebraMap R A a) = algebraMap R Y a :=
    (IsScalarTower.algebraMap_apply R A Y a).symm
  have hp (a : R) : algebraMap R[X] A (C a) = algebraMap R A a :=
    (IsScalarTower.algebraMap_apply R R[X] A a).symm
  simp only [infinityOppositeFactor, map_add, map_mul, map_one, AlgHom.commutes,
    initialInfinityTransition_root, initialInfinityTransition_incidence,
    polynomialOppositeFactor, polynomialSlopeLinear, hp, hc]
  have hv := initialInfinityTransition_x_mul_v W s b3 b4 b6 h3 h4 h6
  change 1 + F u * (g (algebraMap R[X] A r) + algebraMap R Y W.a₁ +
    algebraMap R Y b3 * g (t W s b3 b4 b6)) =
      F u * (g (v W s b3 b4 b6) + (g (algebraMap R[X] A r) +
        (algebraMap R Y W.a₁ + algebraMap R Y b3 * g (t W s b3 b4 b6))))
  linear_combination -hv

variable (hrI : r ∈ I.map C) (hb3 : b3 ∈ I)
local notation "z" => infinityFactorRatioUnit W I hI h2I h3I h4I h6I s b3 r hrI hb3

/-- The full regular infinity ratio has exactly the original tangent-factor denominator. -/
theorem initialInfinityTransition_ratio_denominator : F (z : B) * g U = g V := by
  apply (initialInfinityTransition_x_isUnit W s b3 b4 b6 h3 h4 h6).mul_left_cancel
  have h := congrArg F
    (infinityFactorRatioUnit_denominator W I hI h2I h3I h4I h6I s b3 r hrI hb3)
  rw [map_mul, initialInfinityTransition_oppositeFactor,
    initialInfinityTransition_smallFactor] at h
  calc
    _ = F (z : B) * (F u * g U) := by ring
    _ = _ := h

end FLT.Mazur.WeierstrassModificationX
