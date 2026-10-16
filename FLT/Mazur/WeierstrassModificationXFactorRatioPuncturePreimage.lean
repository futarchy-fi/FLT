/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXNodeOverlapFactorRatioBoundary

/-!
# Exact preimages of both punctures under the full factor-ratio chart

The corrected coordinates differ from the original node coordinates only by
units. Thus the full right edge pulls back to the actual initial overlap,
and the full left edge pulls back to the original incidence open.
-/

@[expose] public noncomputable section
open Polynomial CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (ha : IsUnit W.a₁)
  (s τ : R) (hτ : s = W.a₁ ^ 2 * τ) (b3 b4 b6 : R)
  (r : R[X]) (hr : r ^ 2 + polynomialSlopeLinear W b3 * r =
    polynomialSlopeConstant W b4 b6)
  (I : Ideal R) (hI : IsNilpotent I) (hrI : r ∈ I.map C) (h3 : b3 ∈ I)
local notation "L" => PolynomialNodeOpen W s
local notation "G" => polynomialNodeForwardBase W s b3 b4 b6 r hr I hI hrI h3
local notation "hu" => polynomialNodeForwardBase_opposite_isUnit W s b3 b4 b6 r hr I hI hrI h3
local notation "E" => polynomialFactorRatioEvaluation W ha s τ hτ b3 b4 b6 r hr I hI hrI h3
local notation "F" => polynomialFactorRatioChart W ha s τ hτ b3 b4 b6 r hr I hI hrI h3

/-- The corrected right coordinate vanishes precisely on the original small factor. -/
theorem polynomialFactorRatioEvaluation_right_mem_iff (z : PrimeSpectrum L) :
    E (PolygonSmoothing.rightCoordinate τ) ∈ z.asIdeal ↔
      NodalFiber.tangentQ s W.a₁ ∈ z.asIdeal := by
  rw [polynomialFactorRatioEvaluation_right, polynomialFactorRatioMap_q]
  have hq : G (polynomialSmallFactor W s b3 b4 b6 r) =
      NodalFiber.tangentQ s W.a₁ := polynomialNodeEvaluation_small ..
  rw [hq]
  exact z.asIdeal.mul_unit_mem_iff_mem (Units.isUnit (hu).unit⁻¹)

/-- The entire normalized infinity edge pulls back to the actual full original overlap. -/
theorem polynomialFactorRatioChart_right_preimage :
    F ⁻¹' Set.range (PolygonSmoothing.rightBranchOpen R τ) =
      Set.range (polynomialNodeOverlapInclusion W s) := by
  rw [PolygonSmoothing.rightBranchOpen_range, polynomialNodeOverlapInclusion_range,
    polynomialFactorRatioChart_eq_spec]
  ext z
  exact not_congr
    (polynomialFactorRatioEvaluation_right_mem_iff W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 z)

/-- The corrected left coordinate vanishes precisely on the original first node coordinate. -/
theorem polynomialFactorRatioEvaluation_left_mem_iff (z : PrimeSpectrum L) :
    E (PolygonSmoothing.leftCoordinate τ) ∈ z.asIdeal ↔
      NodalFiber.tangentP s W.a₁ ∈ z.asIdeal := by
  rw [polynomialFactorRatioEvaluation_left, polynomialFactorRatioMap_p_node]
  rw [z.asIdeal.mul_unit_mem_iff_mem hu]
  exact z.asIdeal.unit_mul_mem_iff_mem
    ((((zeroInitialTangentUnit W ha)⁻¹).isUnit.map (algebraMap R L)).pow 2)

/-- The full normalized left edge is the original incidence open, with no lost corrections. -/
theorem polynomialFactorRatioChart_left_preimage :
    F ⁻¹' Set.range (PolygonSmoothing.leftBranchOpen R τ) =
      (PrimeSpectrum.basicOpen (NodalFiber.tangentP s W.a₁) : Set (PrimeSpectrum L)) := by
  rw [PolygonSmoothing.leftBranchOpen_range, polynomialFactorRatioChart_eq_spec]
  ext z
  exact not_congr
    (polynomialFactorRatioEvaluation_left_mem_iff W ha s τ hτ b3 b4 b6 r hr I hI hrI h3 z)

end FLT.Mazur.WeierstrassModificationX
