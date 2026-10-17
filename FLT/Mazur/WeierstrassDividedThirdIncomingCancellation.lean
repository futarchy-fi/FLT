/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdResidualAlgebra
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Simultaneous third cancellation on both incoming edge positions

The negative complementary fields and the positive predecessor fields cancel
the complete third-order errors, including all Laurent coefficients.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 3
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H 3 j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "A" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu

/-- The shared incoming correction leaves exactly the predecessor's full positive substitution. -/
theorem arithmeticThirdIncoming_factorization (b : Bool) :
    (arithmeticThirdLastEdgeEquiv hπ data H j hj u hu 3 b false).trans
        (arithmeticSecondJointIncomingEquiv hπ data H 3 j hj u hu b) =
      twoBranchCorrectionPunctureFactor R π 3 (s b) (P b) true := by
  rw [arithmeticThirdLastEdgeEquiv, arithmeticThirdLastPuncture_third,
    arithmeticThirdLastLayerField_incoming, arithmeticThirdPrecedingPuncture_third,
    arithmeticThirdPrecedingLayerField_outgoing]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticThirdResidualField_subst hπ data H j hj u hu .incoming b
  change (arithmeticSecondJointIncomingEquiv hπ data H 3 j hj u hu b).toAlgHom = _ at h
  change (arithmeticSecondJointIncomingEquiv hπ data H 3 j hj u hu b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticThirdResidualField hπ data H j hj u hu .incoming b)
  linear_combination -hp

/-- Both shared incoming residuals vanish as whole Laurent maps at stage three. -/
theorem arithmeticThirdIncomingEquiv_third (b : Bool) :
    arithmeticThirdIncomingEquiv hπ data H j hj u hu 3 b = AlgEquiv.refl := by
  unfold arithmeticThirdIncomingEquiv
  rw [arithmeticThirdIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

/-- The predecessor incoming correction leaves exactly the earlier positive substitution. -/
theorem arithmeticThirdPreceding_factorization (b : Bool) :
    (arithmeticThirdPrecedingEdgeEquiv hπ data H j hj u hu 3 b).trans
        (arithmeticSecondPrecedingIncomingEquiv hπ data H 3 j hj u hu b) =
      correctionPunctureFactor R π 3 τ (A b) true := by
  rw [arithmeticThirdPrecedingEdgeEquiv, arithmeticThirdPrecedingPuncture_third,
    arithmeticThirdPrecedingLayerField_incoming, arithmeticThirdEarlierPuncture_third]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticThirdResidualField_subst hπ data H j hj u hu .preceding b
  change (arithmeticSecondPrecedingIncomingEquiv hπ data H 3 j hj u hu b).toAlgHom = _ at h
  change (arithmeticSecondPrecedingIncomingEquiv hπ data H 3 j hj u hu b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticThirdResidualField hπ data H j hj u hu .preceding b)
  linear_combination -hp

/-- Both predecessor incoming residuals vanish as whole Laurent maps at stage three. -/
theorem arithmeticThirdPrecedingEquiv_third (b : Bool) :
    arithmeticThirdPrecedingEquiv hπ data H j hj u hu 3 b = AlgEquiv.refl := by
  unfold arithmeticThirdPrecedingEquiv
  rw [arithmeticThirdPreceding_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
