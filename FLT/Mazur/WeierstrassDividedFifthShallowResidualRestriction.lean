/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowIncomingCancellation
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction

/-!
# Full quotient squares for the three fifth residual positions

The exact old and new smoothings survive every puncture substitution and
inverse. Closing, incoming and preceding residuals retain all coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthClosingEquiv arithmeticFourthIncomingEquiv
  arithmeticFourthShallowNeighborIncomingEquiv arithmeticFifthResidualIntegralField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "L" => arithmeticFifthShallowLastEdgeEquiv hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowPrecedingEdgeEquiv hπ data H j hj u hu
local notation "C" => arithmeticFifthShallowClosingEquiv hπ data H j hj u hu
local notation "I" => arithmeticFifthShallowIncomingEquiv hπ data H j hj u hu
local notation "E" => arithmeticFifthShallowPrecedingEquiv hπ data H j hj u hu

/-- Both last-node substitutions in the original edge coordinate retain the quotient square. -/
theorem arithmeticFifthShallowLastEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (L (m + 1) b a).toRingHom =
      (L m b a).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthShallowLastEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ a
  · exact punctureEquiv_invert_naturality f

/-- The predecessor's opposite factor keeps its actual fourth smoothing under restriction. -/
theorem arithmeticFifthShallowPrecedingEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (P (m + 1) b).toRingHom =
      (P m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthShallowPrecedingEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticFourthPrecedingSmoothing_restriction hπ data H j hj u hu m b) _ false
  · exact punctureEquiv_invert_naturality f

/-- Each complete fifth closing residual follows the original arithmetic quotient. -/
theorem arithmeticFifthShallowClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (C (m + 1) b).toRingHom =
      (C m b).toRingHom.comp (coeffMap f) := by
  have hfirst := twoBranchCorrectionRebasedPunctureFactor_symm_restriction R π m _ _
    (arithmeticFourthTerminalSmoothing_restriction hπ data H j hj u hu m)
    (arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu) b
  have hold := arithmeticFourthClosingEquiv_restriction hπ data H j hj u hu m b
  have hlast := symm_naturality f _ _
    (arithmeticFifthShallowLastEdgeEquiv_restriction hπ data H j hj u hu m b true)
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
theorem arithmeticFifthShallowIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthShallowIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthShallowLastEdgeEquiv_restriction hπ data H j hj u hu m b false
    · exact arithmeticFourthIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFourthPrecedingSmoothing_restriction hπ data H j hj u hu m b) _ true

/-- The full preceding residual retains the quotient square of its earlier positive factor. -/
theorem arithmeticFifthShallowPrecedingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthShallowPrecedingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthShallowPrecedingEdgeEquiv_restriction hπ data H j hj u hu m b
    · exact arithmeticFourthShallowNeighborIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFourthShallowNeighborSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
