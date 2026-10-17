/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LaurentCoboundaryBoundary
public import FLT.Mazur.PolygonCompleteIdentityTopCorrection

/-!
# Recovering canonical boundary tails from the original multiplication error

The original obstruction is its canonical correction's literal coboundary.
Mixed coefficients therefore recover both missing tails directly from the
original multiplication. No node extension of the coordinate change is needed
for this recovery. Support bounds on the original error remain to be proved.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open LaurentPolynomial LaurentPairNaturality LaurentCocycleCoefficientRecovery
open PolygonChartScaling PolygonScalingNaturality LaurentScaledEvaluationCoefficients
open PolygonInfinitesimal
open LaurentCoboundaryBoundary LaurentPositivePart LaurentBoundaryVectorField
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n) (m : ℕ)
local notation "O" => completeIdentityFiniteMulObstruction K n h i m
local notation "q" => completeIdentityTopCorrection K n h i m
variable (hm : completeIdentityFiniteMulDefect K n h i m = 0)
include hm

/-- The actual obstruction is the full polynomial coboundary, before any specialization. -/
theorem completeIdentityFiniteMulObstruction_top_coboundary : (O) = coboundary (q) := by
  let u := coordinateUnit (1 : Kˣ)
  let v := coordinateUnit (1 : K[T;T⁻¹]ˣ)
  let U := Units.map (C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]).toMonoidHom u
  have he := completeIdentityTopCorrection_formula K n h i m hm
    ((C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]).comp C) U v
  have hu : eval₂ (C.comp C) U = (C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]) := by
    apply ringHom_ext <;> simp [U, u, eval₂_C, eval₂_T, coordinateUnit]
  have hv : eval₂ (C.comp C) v = coeffMap (C : K →+* K[T;T⁻¹]) := by
    apply ringHom_ext <;> simp [v, eval₂_C, eval₂_T, coordinateUnit]
  have huv : U * v = coordinateUnit u := (coordinate_factor u).symm
  have hpair : pairEval₂ (C.comp C) U v (O) = (O) :=
    RingHom.congr_fun pairEval₂_universal (O)
  have hU : U.val = C (T 1) := by simp [U, u, coordinateUnit]
  have hV : v.val = T 1 := by simp [v, coordinateUnit]
  rw [hpair, hu, hv, huv, hU, hV, mul_comm (T 1) (C (q))] at he
  exact he

/-- Every non-scaling correction coefficient is an explicit original mixed error coefficient. -/
theorem completeIdentityTopCorrection_coeff_from_error (d : ℤ) (hd : d ≠ 1) :
    ((O).coeff d).coeff 1 = (q).coeff d := by
  rw [completeIdentityFiniteMulObstruction_top_coboundary K n h i m hm]
  exact coboundary_coeff_one (q) d hd

/-- Lower support of original multiplication supplies the left canonical boundary extension. -/
theorem completeIdentityTopCorrection_leftTail_of_error
    (hl : ∀ d : ℤ, d ≤ 0 → (O).coeff d = 0) : boundaryTail (q) = 0 := by
  apply boundaryTail_eq_zero_of_coboundary
  simpa only [← completeIdentityFiniteMulObstruction_top_coboundary K n h i m hm] using hl

/-- Upper support of original multiplication supplies the reciprocal canonical extension. -/
theorem completeIdentityTopCorrection_rightTail_of_error
    (hr : ∀ d : ℤ, 2 ≤ d → (O).coeff d = 0) :
    boundaryTail (reciprocalField (q)) = 0 := by
  apply reciprocal_boundaryTail_eq_zero_of_coboundary
  simpa only [← completeIdentityFiniteMulObstruction_top_coboundary K n h i m hm] using hr

/-- Both original error supports force the actual normalized higher correction to vanish. -/
theorem completeIdentityTopCorrection_zero_of_error_support
    (hl : ∀ d : ℤ, d ≤ 0 → (O).coeff d = 0)
    (hr : ∀ d : ℤ, 2 ≤ d → (O).coeff d = 0) : (q) = 0 :=
  eq_zero_of_boundary (q) (positivePart (q)) (positivePart (reciprocalField (q)))
    ((positivePart_toLaurent_iff (q)).mpr
      (completeIdentityTopCorrection_leftTail_of_error K n h i m hm hl))
    ((positivePart_toLaurent_iff _).mpr
      (completeIdentityTopCorrection_rightTail_of_error K n h i m hm hr))
    (positivePart_coeff_zero (q)) (positivePart_coeff_zero (reciprocalField (q)))
    (completeIdentityTopCorrection_at_one K n h i m hm)

/-- Both full original error support bounds imply the next unchanged multiplication law. -/
theorem completeIdentityFiniteLaw_succ_of_error_support
    (hl : ∀ d : ℤ, d ≤ 0 → (O).coeff d = 0)
    (hr : ∀ d : ℤ, 2 ≤ d → (O).coeff d = 0) :
    universalEdgeScaling (Ring K (m + 1)) ≫ completeIdentityStageTorus K n h i (m + 1) =
      completeIdentityFiniteOriginalMul K n h i (m + 1) :=
  (completeIdentityFiniteLaw_succ_iff_correction K n h i m hm).mpr
    (completeIdentityTopCorrection_zero_of_error_support K n h i m hm hl hr)

end FLT.Mazur.PolygonInfinitesimalStages
