/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialResidualAlgebra
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Fifth cancellation of the full depth-one incoming edge

The negative complementary fields and the positive predecessor fields cancel
the complete fifth-order errors, including all Laurent coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthInitialNeighborIncomingEquiv
  arithmeticFifthResidualField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu 5
local notation "P" => arithmeticFifthInitialNeighborIntegralField hπ data H j hj u hu
/-- The shared incoming correction leaves exactly the predecessor's full positive substitution. -/
theorem arithmeticFifthInitialIncoming_factorization (b : Bool) :
    (arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu 5 b false).trans
        (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu 5 b) =
      twoBranchCorrectionPunctureFactor R π 5 (s b) (P b) true := by
  have hin := arithmeticFifthInitialLastLayerField_incoming hπ data H j hj u hu b
  dsimp only at hin
  rw [arithmeticFifthInitialLastEdgeEquiv, arithmeticFifthInitialLastPuncture_fifth,
    hin,
    arithmeticFifthInitialNeighborPuncture_fifth,
    arithmeticFifthInitialNeighborField_outgoing, correctionField_positive,
    arithmeticFifthResidualIntegralField_spec]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .initialIncoming b
  change (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
  change (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFifthResidualField hπ data H j hj u hu .initialIncoming b)
  linear_combination -hp

/-- Both shared incoming residuals vanish as whole Laurent maps at stage five. -/
theorem arithmeticFifthInitialIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthInitialIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthInitialIncomingEquiv
  rw [arithmeticFifthInitialIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
