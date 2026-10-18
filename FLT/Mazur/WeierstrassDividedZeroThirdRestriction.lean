/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdCancellation
public import FLT.Mazur.WeierstrassDividedZeroSecondRestriction

/-!
# Full coefficient squares for the third depth-zero corrections

Both new smoothings, the whole node factors and the full initial residual
retain the original arithmetic coefficient quotients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "a" => arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H j hj u hu
local notation "A" => arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu
local notation "S" => arithmeticZeroThirdLastSmoothing hπ data H j hj u hu
local notation "N" => arithmeticZeroThirdInitialFactor hπ data H j hj u hu
local notation "P" => arithmeticZeroThirdLastFactor hπ data H j hj u hu
local notation "E" => arithmeticZeroThirdInitialEquiv hπ data H j hj u hu

/-- The initial node's full new smoothing is compatible with the original quotient. -/
theorem arithmeticZeroThirdInitialSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticZeroSecondInitialSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both new last node drifts survive the same full coefficient restriction. -/
theorem arithmeticZeroThirdLastSmoothing_restriction (b : Bool) :
    restriction R π m (S (m + 1) b) = S m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b) _

/-- The whole initial node factor retains the quotient square on both coordinates. -/
theorem arithmeticZeroThirdInitialFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticZeroSecondInitialSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticZeroThirdInitialSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticZeroSecondInitialSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both last-node coordinates use their exact old and new coefficient quotients. -/
theorem arithmeticZeroThirdLastFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b)).comp
        (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (ringMap f (S (m + 1) b) (S m b)
        (arithmeticZeroThirdLastSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b) _

local notation "T" => arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu
local notation "t" => arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu
local notation "F" => arithmeticZeroThirdTerminalFactor hπ data H j hj u hu

/-- The terminal retains both old scalar drifts and both new scalar drifts under restriction. -/
theorem arithmeticZeroThirdTerminalSmoothing_restriction : restriction R π m (T (m + 1)) = T m :=
  twoBranchCorrectionRebasedSmoothing_restriction R π m _ _
    (arithmeticZeroSecondTerminalSmoothing_restriction hπ data H j hj u hu m) _

/-- Both terminal coordinates retain the exact quotient square of the rebased full factor. -/
theorem arithmeticZeroThirdTerminalFactor_restriction :
    (ringMap f (T (m + 1)) (T m)
      (arithmeticZeroThirdTerminalSmoothing_restriction hπ data H j hj u hu m)).comp
        (F (m + 1)).toAlgHom.toRingHom =
      (F m).toAlgHom.toRingHom.comp (ringMap f (t (m + 1)) (t m)
        (arithmeticZeroSecondTerminalSmoothing_restriction hπ data H j hj u hu m)) :=
  twoBranchCorrectionRebasedFactor_restriction R π m _ _
    (arithmeticZeroSecondTerminalSmoothing_restriction hπ data H j hj u hu m) _

/-- The full corrected initial residual retains every original coefficient square. -/
theorem arithmeticZeroThirdInitialEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticZeroThirdInitialEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticZeroSecondLastSmoothing_restriction hπ data H j hj u hu m b) _ false
    · exact arithmeticZeroSecondInitialEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticZeroSecondInitialSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
