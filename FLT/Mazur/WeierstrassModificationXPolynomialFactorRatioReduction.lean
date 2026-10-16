/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialFactorRatioMap
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Full factor-ratio congruence with the smoothing-node Möbius map

Both generators, and hence every localized function, agree modulo the extended
original coefficient ideal. The smoothing parameter is retained throughout.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "M" => NodalFiber.TangentOpen τ (-1 : R)
local notation "G" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "F" => polynomialFactorRatioMap W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "a" => zeroInitialTangentUnit W ha
local notation "H" => (NodalFiber.tangentMobiusForward s τ a hτ : M →ₐ[R] L)
local notation "U" => G (polynomialOppositeFactor W s b3 b4 b6 r)
local notation "P" => NodalFiber.tangentP s W.a₁
local notation "Q" => NodalFiber.tangentQ s W.a₁
local notation "A" => algebraMap R L W.a₁
local notation "Ai" => algebraMap R L (↑a⁻¹ : R)
local notation "J" => I.map (algebraMap R L)

/-- The entire opposite-factor correction is in the original extended coefficient ideal. -/
theorem polynomialFactorRatio_opposite_sub_mem : U - (Q + A) ∈ J := by
  have h := evaluatedFactorGap_mem W s b3 b4 b6 r I hrI h3 G
  have hv : G (polynomialSmallFactor W s b3 b4 b6 r) = Q :=
    polynomialNodeEvaluation_small ..
  rw [hv] at h
  convert h using 1
  ring

/-- The first coordinate agrees with the full translated Möbius coordinate modulo the ideal. -/
theorem polynomialFactorRatioMap_p_sub_mem :
    F (NodalFiber.tangentP τ (-1 : R)) - (show L from H (NodalFiber.tangentP τ (-1 : R)))
      ∈ J := by
  rw [polynomialFactorRatioMap_p_node, NodalFiber.tangentMobiusForward_p]
  have he := (J).mul_mem_left (Ai ^ 2 * P)
    (polynomialFactorRatio_opposite_sub_mem W s b3 b4 b6 r hr I hI hrI h3)
  have hi : Ai * A = 1 := by
    rw [← map_mul, show (↑a⁻¹ : R) * W.a₁ = 1 from (a).inv_mul, map_one]
  have hp := NodalFiber.tangent_relation s W.a₁
  have hc : algebraMap R L s = A ^ 2 * algebraMap R L τ := by
    rw [hτ, map_mul, map_pow]
  rw [hc] at hp
  change Ai ^ 2 * P * U - (Ai * P + algebraMap R L τ) ∈ J
  convert he using 1
  linear_combination Ai ^ 2 * hp +
    (Ai * P + (Ai * A + 1) * algebraMap R L τ) * hi

/-- The full ratio and Möbius fraction agree modulo the original ideal. -/
theorem polynomialFactorRatioMap_q_sub_mem :
    F (NodalFiber.tangentQ τ (-1 : R)) - (show L from H (NodalFiber.tangentQ τ (-1 : R)))
      ∈ J := by
  rw [NodalFiber.tangentMobiusForward_q]
  change F (NodalFiber.tangentQ τ (-1 : R)) - NodalFiber.tangentFraction s W.a₁ ∈ J
  have hd := polynomialFactorRatioMap_q_denominator W ha s τ hτ b3 b4 b6 r hr
    I hI hrI h3
  have hv : G (polynomialSmallFactor W s b3 b4 b6 r) = Q :=
    polynomialNodeEvaluation_small ..
  rw [hv] at hd
  have hf := NodalFiber.tangentFraction_denominator s W.a₁
  have he := (J).mul_mem_left (-(F (NodalFiber.tangentQ τ (-1 : R))))
    (polynomialFactorRatio_opposite_sub_mem W s b3 b4 b6 r hr I hI hrI h3)
  apply ((J).mul_unit_mem_iff_mem (NodalFiber.tangent_denominator_isUnit s W.a₁)).mp
  convert he using 1
  linear_combination hd - hf

/-- Agreement on the two coordinates extends to all functions of the tangent localization. -/
theorem polynomialFactorRatioMap_sub_mem (z : M) : F z - (show L from H z) ∈ J := by
  have he : (Ideal.Quotient.mkₐ R J).comp F = (Ideal.Quotient.mkₐ R J).comp H := by
    apply IsLocalization.algHom_ext
      (Submonoid.powers (NodalFiber.q τ + algebraMap R (NodalFiber.Coordinate τ) (-1 : R)))
    apply NodalFiber.hom_ext
    · exact Ideal.Quotient.eq.mpr
        (polynomialFactorRatioMap_p_sub_mem W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)
    · exact Ideal.Quotient.eq.mpr
        (polynomialFactorRatioMap_q_sub_mem W ha s τ hτ b3 b4 b6 r hr I hI hrI h3)
  exact Ideal.Quotient.eq.mp (congrArg (fun k : M →ₐ[R] L ⧸ J ↦ k z) he)

end FLT.Mazur.WeierstrassModificationX
