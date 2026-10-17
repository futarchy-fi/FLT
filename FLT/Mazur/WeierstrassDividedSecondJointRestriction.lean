/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointResiduals
public import FLT.Mazur.WeierstrassDividedSecondResidualRestriction

/-!
# Quotient squares for simultaneous second corrections

Both punctures of each shared node, the predecessor correction, and all four
recomputed transitions preserve the original arithmetic coefficient maps.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open PolygonScalingNaturality LaurentUnitSubstitutionNaturality
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "f" => AlgHom.toRingHom (restriction R π m)
local notation "K" => fun k ↦ arithmeticSecondJointEdgeEquiv hπ data H k j hj u hu
local notation "P" => fun k ↦ arithmeticSecondPrecedingPuncture hπ data H k j hj u hu
local notation "D" => fun k ↦ arithmeticSecondJointClosingEquiv hπ data H k j hj u hu
local notation "I" => fun k ↦ arithmeticSecondJointIncomingEquiv hπ data H k j hj u hu

/-- Both shared-node edge maps retain the original full quotient square. -/
theorem arithmeticSecondJointEdgeEquiv_restriction (b a : Bool) :
    (coeffMap f).comp (K (m + 1) b a).toAlgHom.toRingHom =
      (K m b a).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondJointEdgeEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact punctureEquiv_invert_naturality f
    · unfold twoBranchCorrectionPunctureFactor
      apply punctureEquiv_trans_naturality
      · exact correctionPunctureFactor_restriction R π m _ _
          (correctionSmoothing_restriction R π m _ _
            (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _) _ a
      · exact correctionPunctureFactor_restriction R π m _ _
          (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ (!a)
  · exact punctureEquiv_invert_naturality f

/-- The predecessor's entire outgoing correction has the same original coefficient square. -/
theorem arithmeticSecondPrecedingPuncture_restriction (b : Bool) :
    (coeffMap f).comp (P (m + 1) b).toAlgHom.toRingHom =
      (P m b).toAlgHom.toRingHom.comp (coeffMap f) :=
  correctionPunctureFactor_restriction R π m _ _
    (arithmeticInitialMobiusSmoothing_restriction W H.a1_unit (π ^ 1) π m) _ true

/-- Every complete jointly corrected closing transition descends along the arithmetic quotient. -/
theorem arithmeticSecondJointClosingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (D (m + 1) b).toAlgHom.toRingHom =
      (D m b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondJointClosingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact symm_naturality f _ _
        (arithmeticSecondResidualLiftTerminalPuncture_restriction hπ data H m j hj u hu b)
    · exact arithmeticResidualLiftClosingEquiv_restriction hπ data H m j hj u hu b
  · exact symm_naturality f _ _
      (arithmeticSecondJointEdgeEquiv_restriction hπ data H m j hj u hu b true)

/-- Every complete jointly corrected incoming transition has the original full quotient square. -/
theorem arithmeticSecondJointIncomingEquiv_restriction (b : Bool) :
    (coeffMap f).comp (I (m + 1) b).toAlgHom.toRingHom =
      (I m b).toAlgHom.toRingHom.comp (coeffMap f) := by
  unfold arithmeticSecondJointIncomingEquiv
  apply punctureEquiv_trans_naturality
  · apply punctureEquiv_trans_naturality
    · exact arithmeticSecondJointEdgeEquiv_restriction hπ data H m j hj u hu b false
    · exact arithmeticResidualLiftEdgeEquiv_restriction hπ data H m j hj u hu b false
  · exact symm_naturality f _ _
      (arithmeticSecondPrecedingPuncture_restriction hπ data H m j hj u hu b)

end FLT.Mazur.WeierstrassDividedDepth
