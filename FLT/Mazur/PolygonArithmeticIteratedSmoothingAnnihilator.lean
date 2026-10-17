/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticIteratedNodeCorrection
public import FLT.Mazur.PolygonArithmeticTwoBranchRebase

/-!
# Annihilators survive every smoothing drift

Multiplication by each exact scalar drift preserves every annihilator of the
original smoothing. This supplies higher-layer hypotheses after any finite
number of node corrections, without expanding their accumulated drifts.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonArithmeticStages
open PolygonSmoothing
variable (R : Type*) [CommRing R] (π : R) (m : ℕ)
  (t e : Quotient R π m)

/-- A whole-node correction preserves every annihilator of the input smoothing. -/
theorem correctionSmoothing_annihilated (ht : e * t = 0) (q : R[T;T⁻¹]) :
    e * correctionSmoothing R π m t q = 0 := by
  unfold correctionSmoothing
  rw [mul_left_comm e, ht, mul_zero]

/-- A two-branch correction preserves the same annihilator on its changed smoothing. -/
theorem twoBranchCorrectionSmoothing_annihilated (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) :
    e * twoBranchCorrectionSmoothing R π m t q = 0 := by
  rw [twoBranchCorrectionSmoothing_eq_drift, mul_left_comm e, ht, mul_zero]

/-- The inverse scalar drift needed by the terminal node also preserves annihilation. -/
theorem twoBranchCorrectionRebasedSmoothing_annihilated (ht : e * t = 0)
    (q : Bool → R[T;T⁻¹]) :
    e * twoBranchCorrectionRebasedSmoothing R π m t q = 0 := by
  unfold twoBranchCorrectionRebasedSmoothing
  rw [mul_left_comm e, ht, mul_zero]

/-- Every finite sequence of full corrections preserves the original annihilator. -/
theorem iteratedCorrectionSmoothing_annihilated (ht : e * t = 0)
    (q : ℕ → Bool → R[T;T⁻¹]) (k : ℕ) :
    e * iteratedCorrectionSmoothing R π m t q k = 0 := by
  induction k with
  | zero => exact ht
  | succ k ih => exact twoBranchCorrectionSmoothing_annihilated R π m _ e ih (q k)

end FLT.Mazur.PolygonArithmeticStages
