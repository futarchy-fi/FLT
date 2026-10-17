/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialCancellation
public import FLT.Mazur.WeierstrassDividedFourthResidualRestriction

/-!
# Full coefficient squares for the fourth initial corrections

Both new smoothings, the whole node factors and both incident edge residuals
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
local notation "a" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFourthInitialSmoothing hπ data H j hj u hu
local notation "S" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFourthInitialFactor hπ data H j hj u hu
local notation "P" => arithmeticFourthInitialNeighborFactor hπ data H j hj u hu
local notation "E" => arithmeticFourthInitialEquiv hπ data H j hj u hu
local notation "I" => arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu

/-- The initial node's full new smoothing is compatible with the original quotient. -/
theorem arithmeticFourthInitialSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both new predecessor drifts survive the same full coefficient restriction. -/
theorem arithmeticFourthInitialNeighborSmoothing_restriction (b : Bool) :
    restriction R π m (S (m + 1) b) = S m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _

/-- The whole initial node factor retains the quotient square on both coordinates. -/
theorem arithmeticFourthInitialFactor_restriction (b : Bool) :
    (ringMap f (a (m + 1) b) (a m b)
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- Both neighboring coordinates use their exact old and new coefficient quotients. -/
theorem arithmeticFourthInitialNeighborFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b)).comp
        (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (ringMap f (S (m + 1) b) (S m b)
        (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _

/-- The full corrected initial residual retains every original coefficient square. -/
theorem arithmeticFourthInitialEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthInitialEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _ false
    · exact arithmeticThirdInitialEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _ true

/-- The shared incoming residual uses that same full corrected predecessor under restriction. -/
theorem arithmeticFourthInitialNeighborIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthInitialNeighborIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFourthLastEdgeEquiv_restriction hπ data H j hj u hu m b false
    · exact arithmeticThirdIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticThirdPrecedingSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
