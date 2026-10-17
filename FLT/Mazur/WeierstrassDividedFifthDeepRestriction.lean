/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthDeepCancellation
public import FLT.Mazur.PolygonArithmeticTwoBranchPunctureRestriction
public import FLT.Mazur.PolygonArithmeticHigherPunctureIdentification

/-!
# Concrete coefficient squares for the full fifth outer node factors

All three retained nodes and both common residuals keep the original coefficient
quotient, with the complete fourth and fifth smoothings on their two sides.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "s" => arithmeticFifthDeepInput hπ data H j hj u hu
local notation "t" => arithmeticFifthDeepSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFifthDeepFactor hπ data H j hj u hu
local notation "P" => fun v ↦ arithmeticFifthPairedIntegralField hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v)
local notation "C" => fun v m b ↦ arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu
  (fifthDeepOutgoing v) (fifthDeepIncoming v) m (s v m b) b
variable (m : ℕ)
local notation "f" => AlgHom.toRingHom (restriction R π m)

/-- The new exact scalar drift at each node commutes with the original quotient. -/
theorem arithmeticFifthDeepSmoothing_restriction (v : FifthDeepNode) (b : Bool) :
    restriction R π m (t v (m + 1) b) = t v m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticFifthDeepInput_restriction hπ data H j hj u hu v m b) _

/-- Each entire node factor retains both concrete coordinate quotient squares. -/
theorem arithmeticFifthDeepFactor_restriction (v : FifthDeepNode) (b : Bool) :
    (ringMap f (s v (m + 1) b) (s v m b)
      (arithmeticFifthDeepInput_restriction hπ data H j hj u hu v m b)).comp
        (N v (m + 1) b).toAlgHom.toRingHom =
      (N v m b).toAlgHom.toRingHom.comp (ringMap f (t v (m + 1) b) (t v m b)
        (arithmeticFifthDeepSmoothing_restriction hπ data H j hj u hu m v b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticFifthDeepInput_restriction hπ data H j hj u hu v m b) _

/-- Both full Laurent punctures retain their original coefficient maps. -/
theorem arithmeticFifthDeepPuncture_restriction (v : FifthDeepNode) (b a : Bool) :
    (coeffMap f).comp
        (twoBranchCorrectionPunctureFactor R π (m + 1) (s v (m + 1) b) (P v b) a).toRingHom =
      (twoBranchCorrectionPunctureFactor R π m (s v m b) (P v b) a).toRingHom.comp
        (coeffMap f) :=
  twoBranchCorrectionPunctureFactor_restriction R π m _ _
    (arithmeticFifthDeepInput_restriction hπ data H j hj u hu v m b) _ a

/-- Reciprocal incoming coordinates retain the same full coefficient square. -/
theorem arithmeticFifthDeepEdgeEquiv_restriction (v : FifthDeepNode) (b : Bool) :
    (coeffMap f).comp (C v (m + 1) b).toRingHom =
      (C v m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFifthPairedEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact arithmeticFifthDeepPuncture_restriction hπ data H j hj u hu m v b false
  · exact punctureEquiv_invert_naturality f

/-- The whole preceding residual retains the quotient on all three full substitutions. -/
theorem arithmeticFifthDeepPrecedingEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticFifthDeepPrecedingEquiv hπ data H j hj u hu (m + 1) b).toRingHom =
      (arithmeticFifthDeepPrecedingEquiv hπ data H j hj u hu m b).toRingHom.comp
        (coeffMap f) := by
  unfold arithmeticFifthDeepPrecedingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthDeepEdgeEquiv_restriction hπ data H j hj u hu m .predecessor b
    · exact arithmeticFourthOuterPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFifthDeepInput_restriction hπ data H j hj u hu .outer m b) _ true

/-- The simultaneous outer incoming residual retains the identical coefficient square. -/
theorem arithmeticFifthDeepOuterIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp
        (arithmeticFifthDeepOuterIncomingEquiv hπ data H j hj u hu (m + 1) b).toRingHom =
      (arithmeticFifthDeepOuterIncomingEquiv hπ data H j hj u hu m b).toRingHom.comp
        (coeffMap f) := by
  unfold arithmeticFifthDeepOuterIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFifthDeepEdgeEquiv_restriction hπ data H j hj u hu m .outer b
    · exact arithmeticFourthOuterIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticFifthDeepInput_restriction hπ data H j hj u hu .farther m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
