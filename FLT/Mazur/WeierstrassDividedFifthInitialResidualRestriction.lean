/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialIncomingCancellation
public import FLT.Mazur.WeierstrassDividedFifthInitialCancellation
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction
public import FLT.Mazur.WeierstrassDividedFifthInitialRestriction

/-!
# Full quotient squares for the depth-one fifth residuals

The exact old and new smoothings survive every puncture substitution and
inverse. Closing, incoming and initial residuals retain all coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthClosingEquiv
  arithmeticFourthInitialNeighborIncomingEquiv
  arithmeticFourthShallowNeighborIncomingEquiv arithmeticFifthResidualIntegralField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticFifthInitialClosingEquiv hπ data H j hj u hu
local notation "I" => arithmeticFifthInitialIncomingEquiv hπ data H j hj u hu

/-- Both last-node substitutions in the original edge coordinate retain the quotient square. -/
theorem arithmeticFifthInitialLastEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (L (m + 1) b a).toRingHom =
      (L m b a).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthInitialLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
  · exact punctureEquiv_invert_naturality f

/-- Each complete fifth closing residual follows the original arithmetic quotient. -/
theorem arithmeticFifthInitialClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  have hfirst := twoBranchCorrectionRebasedPunctureFactor_symm_restriction R π m _ _
    (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m)
    (arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu) b
  have hold := arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu m b
  have hlast := symm_naturality f _ _
    (arithmeticFifthInitialLastEdgeEquiv_restriction hπ data H j hj u hu m b true)
  apply RingHom.ext
  intro z
  let a := (twoBranchCorrectionRebasedPunctureFactor R π (m + 1)
    (arithmeticFourthTerminalSmoothing hπ data H j hj u hu (m + 1))
    (arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu) b).symm
  let old := arithmeticFourthClosingEquiv hπ data H j hj u hu (m + 1) b
  exact (DFunLike.congr_fun hlast (old (a z))).trans
    (congrArg (L m b true).symm
      ((DFunLike.congr_fun hold (a z)).trans
        (congrArg (arithmeticFourthClosingEquiv hπ data H j hj u hu m b)
          (DFunLike.congr_fun hfirst z))))

/-- Both full incoming residuals use the same quotient on all three endpoint factors. -/
theorem arithmeticFifthInitialIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthInitialIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthInitialLastEdgeEquiv_restriction hπ data H j hj u hu m b false
    · exact arithmeticFourthInitialNeighborIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b) _ true

/-- The original initial edge retains the full fifth coefficient square. -/
theorem arithmeticFifthInitialEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticFifthInitialEquiv hπ data H j hj u hu (m + 1) b).toRingHom =
      (arithmeticFifthInitialEquiv hπ data H j hj u hu m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthInitialEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticFourthInitialNeighborSmoothing_restriction hπ data H j hj u hu m b) _ false
    · exact arithmeticFourthInitialEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFourthInitialSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
