/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterNodes
public import FLT.Mazur.WeierstrassDividedFourthIncomingCancellation

/-!
# Simultaneous cancellation on the earlier and farther retained edges

One full earlier factor cancels its incoming error and preserves the preceding
edge cancellation. The farther retained factor supplies the positive incoming part.
These factors still need installation at their actual global labels.
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
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "P" => arithmeticFourthOuterIntegralField hπ data H j hj u hu
local notation "A" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- Express the earlier incoming factor in the actual reciprocal retained coordinate. -/
def arithmeticFourthOuterEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m (s b) (P b) false)).trans invert

/-- The complete further incoming residual retains all three full substitutions. -/
def arithmeticFourthOuterIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthOuterEdgeEquiv hπ data H j hj u hu m b).trans
      (arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu m b)).trans
    (correctionPunctureFactor R π m τ (A b) true).symm

/-- The preceding residual uses the same earlier whole-node factor on its other branch. -/
def arithmeticFourthOuterPrecedingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthPrecedingEdgeEquiv hπ data H j hj u hu m b).trans
      (arithmeticThirdPrecedingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

omit m in
/-- The complementary incoming field leaves precisely the farther positive factor. -/
theorem arithmeticFourthOuterIncoming_factorization (b : Bool) :
    (arithmeticFourthOuterEdgeEquiv hπ data H j hj u hu 4 b).trans
        (arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu 4 b) =
      correctionPunctureFactor R π 4
        (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4) (A b) true := by
  rw [arithmeticFourthOuterEdgeEquiv, arithmeticFourthOuterPuncture_fourth,
    arithmeticFourthOuterField_incoming_spec, arithmeticFourthFartherPuncture_fourth]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFourthResidualField_subst hπ data H j hj u hu .earlierIncoming b
  change (arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu 4 b).toAlgHom = _ at h
  change (arithmeticThirdEarlierIncomingEquiv hπ data H j hj u hu 4 b).toAlgHom.comp
    (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
      (-reciprocalField (nonpositivePart _))).comp invert.toAlgHom)) = _
  rw [h, LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_neg,
    reciprocalField_involutive, LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  have hp := parts_add (arithmeticFourthResidualField hπ data H j hj u hu .earlierIncoming b)
  linear_combination -hp

omit m in
/-- The entire further retained incoming residual is identity at layer four. -/
theorem arithmeticFourthOuterIncomingEquiv_fourth (b : Bool) :
    arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthOuterIncomingEquiv
  rw [arithmeticFourthOuterIncoming_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

omit m in
/-- The same full earlier node simultaneously cancels its preceding edge at layer four. -/
theorem arithmeticFourthOuterPrecedingEquiv_fourth (b : Bool) :
    arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthOuterPrecedingEquiv
  rw [arithmeticFourthPreceding_factorization, arithmeticFourthEarlierPuncture_fourth,
    arithmeticFourthOuterPuncture_fourth]
  have h : correctionField R π 4 (arithmeticFourthOuterField hπ data H j hj u hu b true) =
      positivePart (arithmeticFourthResidualField hπ data H j hj u hu .preceding b) := by
    change correctionField R π 4 (positivePart _) = _
    rw [correctionField_positive, arithmeticFourthResidualIntegralField_spec]
  rw [h]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
