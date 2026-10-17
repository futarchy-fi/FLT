/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterCancellation
public import FLT.Mazur.WeierstrassDividedFourthResidualRestriction

/-!
# Full coefficient quotients for the further fourth corrections

Both changing smoothings, their full factors, and their simultaneous residuals
commute with the original arithmetic coefficient quotient.
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
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu
local notation "τ" => fun k ↦ arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π k
local notation "P" => arithmeticFourthOuterSmoothing hπ data H j hj u hu
local notation "A" => arithmeticFourthFartherSmoothing hπ data H j hj u hu
local notation "N" => arithmeticFourthOuterFactor hπ data H j hj u hu
local notation "F" => arithmeticFourthFartherFactor hπ data H j hj u hu
local notation "E" => arithmeticFourthOuterEdgeEquiv hπ data H j hj u hu
local notation "I" => arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu
local notation "B" => arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu

/-- Both fourth drifts of the earlier node commute with the actual coefficient quotient. -/
theorem arithmeticFourthOuterSmoothing_restriction (b : Bool) :
    restriction R π m (P (m + 1) b) = P m b :=
  twoBranchCorrectionSmoothing_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- The farther node's scalar drift commutes with the same quotient. -/
theorem arithmeticFourthFartherSmoothing_restriction (b : Bool) :
    restriction R π m (A (m + 1) b) = A m b :=
  correctionSmoothing_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- The earlier whole-node factor retains both coordinate quotient squares. -/
theorem arithmeticFourthOuterFactor_restriction (b : Bool) :
    (ringMap f (s (m + 1) b) (s m b)
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b)).comp
        (N (m + 1) b).toAlgHom.toRingHom =
      (N m b).toAlgHom.toRingHom.comp (ringMap f (P (m + 1) b) (P m b)
        (arithmeticFourthOuterSmoothing_restriction hπ data H j hj u hu m b)) :=
  twoBranchCorrectionNodeFactor_restriction R π m _ _
    (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _

/-- The farther whole-node factor retains its complete coefficient square. -/
theorem arithmeticFourthFartherFactor_restriction (b : Bool) :
    (ringMap f (τ (m + 1)) (τ m)
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m)).comp
        (F (m + 1) b).toAlgHom.toRingHom =
      (F m b).toAlgHom.toRingHom.comp (ringMap f (A (m + 1) b) (A m b)
        (arithmeticFourthFartherSmoothing_restriction hπ data H j hj u hu m b)) :=
  correctionNodeFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _

/-- The reciprocal incoming factor respects the full arithmetic quotient. -/
theorem arithmeticFourthOuterEdgeEquiv_restriction (b : Bool) :
    (coeffMap f).comp (E (m + 1) b).toRingHom =
      (E m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthOuterEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · exact twoBranchCorrectionPunctureFactor_restriction R π m _ _
        (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _ false
  · exact punctureEquiv_invert_naturality f

/-- The entire further incoming residual retains its coefficient square. -/
theorem arithmeticFourthOuterIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toRingHom =
      (I m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthOuterIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFourthOuterEdgeEquiv_restriction hπ data H j hj u hu m b
    · exact arithmeticThirdEarlierIncomingEquiv_restriction hπ data H j hj u hu m b
  · exact correctionPunctureFactor_symm_restriction R π m _ _
      (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

/-- The other incident residual uses that same complete quotient square. -/
theorem arithmeticFourthOuterPrecedingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (B (m + 1) b).toRingHom =
      (B m b).toRingHom.comp (coeffMap f) := by
  unfold arithmeticFourthOuterPrecedingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticFourthPrecedingEdgeEquiv_restriction hπ data H j hj u hu m b
    · exact arithmeticThirdPrecedingEquiv_restriction hπ data H j hj u hu m b
  · exact twoBranchCorrectionPunctureFactor_symm_restriction R π m _ _
      (arithmeticThirdEarlierSmoothing_restriction hπ data H j hj u hu m b) _ true

end FLT.Mazur.WeierstrassDividedDepth
