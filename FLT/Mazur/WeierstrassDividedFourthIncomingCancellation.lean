/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthResidualAlgebra
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Simultaneous fourth cancellation on both incoming edge positions

The negative complementary fields and the positive predecessor fields cancel
the complete fourth-order errors, including all Laurent coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "sE" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu 4
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 4
local notation "P" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu
local notation "A" => arithmeticFourthEarlierIntegralField hπ data H j hj u hu

/-- The shared incoming correction leaves exactly the predecessor's full positive substitution. -/
theorem arithmeticFourthIncoming_factorization (b : Bool) :
    (arithmeticFourthLastEdgeEquiv hπ data H j hj u hu 4 b false).trans
        (arithmeticThirdIncomingEquiv hπ data H j hj u hu 4 b) =
      twoBranchCorrectionPunctureFactor R π 4 (s b) (P b) true := by
  have hin := arithmeticFourthLastLayerField_incoming hπ data H j hj u hu b
  have hout := arithmeticFourthPrecedingLayerField_outgoing hπ data H j hj u hu b
  dsimp only at hin hout
  rw [arithmeticFourthLastEdgeEquiv, arithmeticFourthLastPuncture_fourth,
    hin,
    arithmeticFourthPrecedingPuncture_fourth,
    hout]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFourthResidualField_subst hπ data H j hj u hu .incoming b
  change (arithmeticThirdIncomingEquiv hπ data H j hj u hu 4 b).toAlgHom = _ at h
  change (arithmeticThirdIncomingEquiv hπ data H j hj u hu 4 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFourthResidualField hπ data H j hj u hu .incoming b)
  linear_combination -hp

/-- Both shared incoming residuals vanish as whole Laurent maps at stage four. -/
theorem arithmeticFourthIncomingEquiv_fourth (b : Bool) :
    arithmeticFourthIncomingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthIncomingEquiv
  rw [arithmeticFourthIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

/-- The predecessor incoming correction leaves exactly the earlier positive substitution. -/
theorem arithmeticFourthPreceding_factorization (b : Bool) :
    (arithmeticFourthPrecedingEdgeEquiv hπ data H j hj u hu 4 b).trans
        (arithmeticThirdPrecedingEquiv hπ data H j hj u hu 4 b) =
      correctionPunctureFactor R π 4 (sE b) (A b) true := by
  have hin := arithmeticFourthPrecedingLayerField_incoming hπ data H j hj u hu b
  dsimp only at hin
  rw [arithmeticFourthPrecedingEdgeEquiv, arithmeticFourthPrecedingPuncture_fourth,
    hin,
    arithmeticFourthEarlierPuncture_fourth]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFourthResidualField_subst hπ data H j hj u hu .preceding b
  change (arithmeticThirdPrecedingEquiv hπ data H j hj u hu 4 b).toAlgHom = _ at h
  change (arithmeticThirdPrecedingEquiv hπ data H j hj u hu 4 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFourthResidualField hπ data H j hj u hu .preceding b)
  linear_combination -hp

/-- Both predecessor incoming residuals vanish as whole Laurent maps at stage four. -/
theorem arithmeticFourthPrecedingEquiv_fourth (b : Bool) :
    arithmeticFourthPrecedingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthPrecedingEquiv
  rw [arithmeticFourthPreceding_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
