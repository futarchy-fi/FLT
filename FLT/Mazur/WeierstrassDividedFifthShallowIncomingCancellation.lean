/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowResidualAlgebra
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Simultaneous fifth cancellation on both incoming edge positions

The negative complementary fields and the positive predecessor fields cancel
the complete fifth-order errors, including all Laurent coefficients.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
open LaurentBoundaryVectorField LaurentBoundaryCorrectionSplit
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] arithmeticFourthIncomingEquiv
  arithmeticFourthShallowNeighborIncomingEquiv arithmeticFifthResidualField
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "sE" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu 5
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu 5
local notation "P" => arithmeticFifthShallowPrecedingIntegralField hπ data H j hj u hu
local notation "A" => arithmeticFifthShallowNeighborIntegralField hπ data H j hj u hu

/-- The shared incoming correction leaves exactly the predecessor's full positive substitution. -/
theorem arithmeticFifthShallowIncoming_factorization (b : Bool) :
    (arithmeticFifthShallowLastEdgeEquiv hπ data H j hj u hu 5 b false).trans
        (arithmeticFourthIncomingEquiv hπ data H j hj u hu 5 b) =
      twoBranchCorrectionPunctureFactor R π 5 (s b) (P b) true := by
  have hin := arithmeticFifthShallowLastLayerField_incoming hπ data H j hj u hu b
  have hout := arithmeticFifthShallowPrecedingLayerField_outgoing hπ data H j hj u hu b
  dsimp only at hin hout
  rw [arithmeticFifthShallowLastEdgeEquiv, arithmeticFifthShallowLastPuncture_fifth,
    hin,
    arithmeticFifthShallowPrecedingPuncture_fifth,
    hout]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .incoming b
  change (arithmeticFourthIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
  change (arithmeticFourthIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFifthResidualField hπ data H j hj u hu .incoming b)
  linear_combination -hp

/-- Both shared incoming residuals vanish as whole Laurent maps at stage five. -/
theorem arithmeticFifthShallowIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthShallowIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthShallowIncomingEquiv
  rw [arithmeticFifthShallowIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

/-- The predecessor incoming correction leaves exactly the earlier positive substitution. -/
theorem arithmeticFifthShallowPreceding_factorization (b : Bool) :
    (arithmeticFifthShallowPrecedingEdgeEquiv hπ data H j hj u hu 5 b).trans
        (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu 5 b) =
      twoBranchCorrectionPunctureFactor R π 5 (sE b) (A b) true := by
  have hin := arithmeticFifthShallowPrecedingLayerField_incoming hπ data H j hj u hu b
  dsimp only at hin
  rw [arithmeticFifthShallowPrecedingEdgeEquiv, arithmeticFifthShallowPrecedingPuncture_fifth,
    hin,
    arithmeticFifthShallowNeighborPuncture_fifth,
    arithmeticFifthShallowNeighborField_outgoing, arithmeticFifthShallowEarlierField,
    correctionField_positive, arithmeticFifthResidualIntegralField_spec]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .shallowIncoming b
  change (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
  change (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu 5 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFifthResidualField hπ data H j hj u hu .shallowIncoming b)
  linear_combination -hp

/-- Both predecessor incoming residuals vanish as whole Laurent maps at stage five. -/
theorem arithmeticFifthShallowPrecedingEquiv_fifth (b : Bool) :
    arithmeticFifthShallowPrecedingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthShallowPrecedingEquiv
  rw [arithmeticFifthShallowPreceding_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
