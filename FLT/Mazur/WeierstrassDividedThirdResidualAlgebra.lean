/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdLayerFieldIdentification
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Full third residuals from the actual whole-node puncture factors

The three edge positions use the same shared node corrections and the exact
old smoothing at each endpoint. Both closing residuals vanish at stage three.
These algebra maps still require installation in the third global atlas.
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
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "t" => arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticThirdLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticThirdTerminalIntegralField hπ data H j hj u hu
local notation "A" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu

/-- Both last-node substitutions expressed in the original inverse edge coordinates. -/
def arithmeticThirdLastEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m τ (V b) a)).trans invert

/-- The predecessor's opposite substitution in its original incoming edge coordinate. -/
def arithmeticThirdPrecedingEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m (s b) (P b) false)).trans invert

/-- The full closing residual after both actual third endpoint substitutions. -/
def arithmeticThirdClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionRebasedPunctureFactor R π m t T b).symm.trans
      (arithmeticSecondJointClosingEquiv hπ data H m j hj u hu b)).trans
    (arithmeticThirdLastEdgeEquiv hπ data H j hj u hu m b true).symm

/-- The shared incoming residual uses the same last-node factor as the closing edge. -/
def arithmeticThirdIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticThirdLastEdgeEquiv hπ data H j hj u hu m b false).trans
      (arithmeticSecondJointIncomingEquiv hπ data H m j hj u hu b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

/-- The earlier edge uses the same predecessor factor as the shared incoming edge. -/
def arithmeticThirdPrecedingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticThirdPrecedingEdgeEquiv hπ data H j hj u hu m b).trans
      (arithmeticSecondPrecedingIncomingEquiv hπ data H m j hj u hu b)).trans
    (correctionPunctureFactor R π m τ (A b) true).symm

omit m in
/-- The full old closing residual factors through the actual third node substitutions. -/
theorem arithmeticThirdClosing_factorization (b : Bool) :
    arithmeticSecondJointClosingEquiv hπ data H 3 j hj u hu b =
      (twoBranchCorrectionRebasedPunctureFactor R π 3
        (arithmeticSecondResidualLiftSmoothing hπ data H j hj u hu 3) T b).trans
        (arithmeticThirdLastEdgeEquiv hπ data H j hj u hu 3 b true) := by
  rw [arithmeticThirdLastEdgeEquiv, arithmeticThirdTerminalPuncture_third,
    arithmeticThirdLastPuncture_third, arithmeticThirdLastLayerField_outgoing]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticThirdResidualField_subst hπ data H j hj u hu .closing b
  change (arithmeticSecondJointClosingEquiv hπ data H 3 j hj u hu b).toAlgHom = _ at h
  rw [h]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (reciprocalField (nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (parts_add (arithmeticThirdResidualField hπ data H j hj u hu .closing b)).symm.trans
    (add_comm _ _)

omit m in
/-- Both closing residuals vanish as complete Laurent maps on the third layer. -/
theorem arithmeticThirdClosingEquiv_third (b : Bool) :
    arithmeticThirdClosingEquiv hπ data H j hj u hu 3 b = AlgEquiv.refl := by
  unfold arithmeticThirdClosingEquiv
  rw [arithmeticThirdClosing_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
