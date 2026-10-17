/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdIncomingCancellation
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Full quotient squares for the three third residual positions

The exact old and new smoothings survive every puncture substitution and
inverse. Closing, incoming and preceding residuals retain all coefficients.
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
local notation "L" => arithmeticThirdLastEdgeEquiv hπ data H j hj u hu
local notation "P" => arithmeticThirdPrecedingEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticThirdClosingEquiv hπ data H j hj u hu
local notation "I" => arithmeticThirdIncomingEquiv hπ data H j hj u hu
local notation "E" => arithmeticThirdPrecedingEquiv hπ data H j hj u hu

/-- Both last-node substitutions in the original edge coordinate retain the quotient square. -/
theorem arithmeticThirdLastEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (L (m + 1) b a).toRingHom =
      (L m b a).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
  · exact punctureEquiv_invert_naturality f

/-- The predecessor's opposite factor keeps its actual second smoothing under restriction. -/
theorem arithmeticThirdPrecedingEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (P (m + 1) b).toRingHom =
      (P m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdPrecedingEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b) _ false
  · exact punctureEquiv_invert_naturality f

/-- Each complete third closing residual follows the original arithmetic quotient. -/
theorem arithmeticThirdClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionRebasedPunctureFactor_symm_restriction R π m _ _
        (arithmeticSecondResidualLiftSmoothing_restriction hπ data H j hj u hu m) _ b
    · exact arithmeticSecondJointClosingEquiv_restriction hπ data H m j hj u hu b
  · exact symm_naturality f _ _
      (arithmeticThirdLastEdgeEquiv_restriction hπ data H j hj u hu m b true)

/-- Both full incoming residuals use the same quotient on all three endpoint factors. -/
theorem arithmeticThirdIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticThirdLastEdgeEquiv_restriction hπ data H j hj u hu m b false
    · exact arithmeticSecondJointIncomingEquiv_restriction hπ data H m j hj u hu b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticSecondPrecedingSmoothing_restriction hπ data H m j hj u hu b) _ true

/-- The full preceding residual retains the quotient square of its earlier positive factor. -/
theorem arithmeticThirdPrecedingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticThirdPrecedingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticThirdPrecedingEdgeEquiv_restriction hπ data H j hj u hu m b
    · exact arithmeticSecondPrecedingIncomingEquiv_restriction hπ data H m j hj u hu b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

end FLT.Mazur.WeierstrassDividedDepth
