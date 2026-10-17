/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthLayerFieldIdentification
public import FLT.Mazur.PolygonSmoothingPunctureIdentification

/-!
# Full fourth residuals from the actual whole-node puncture factors

The three edge positions use the same shared node corrections and the exact
old smoothing at each endpoint. Both closing residuals vanish at stage four.
These algebra maps still require installation in the fourth global atlas.
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
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticThirdTerminalSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFourthTerminalIntegralField hπ data H j hj u hu
local notation "sE" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticFourthEarlierIntegralField hπ data H j hj u hu

/-- Both last-node substitutions expressed in the original inverse edge coordinates. -/
def arithmeticFourthLastEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m τ (V b) a)).trans invert

/-- The predecessor's opposite substitution in its original incoming edge coordinate. -/
def arithmeticFourthPrecedingEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m (s b) (P b) false)).trans invert

/-- The full closing residual after both actual fourth endpoint substitutions. -/
def arithmeticFourthClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionRebasedPunctureFactor R π m t T b).symm.trans
      (arithmeticThirdClosingEquiv hπ data H j hj u hu m b)).trans
    (arithmeticFourthLastEdgeEquiv hπ data H j hj u hu m b true).symm

/-- The shared incoming residual uses the same last-node factor as the closing edge. -/
def arithmeticFourthIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthLastEdgeEquiv hπ data H j hj u hu m b false).trans
      (arithmeticThirdIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

/-- The earlier edge uses the same predecessor factor as the shared incoming edge. -/
def arithmeticFourthPrecedingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthPrecedingEdgeEquiv hπ data H j hj u hu m b).trans
      (arithmeticThirdPrecedingEquiv hπ data H j hj u hu m b)).trans
    (correctionPunctureFactor R π m (sE b) (A b) true).symm

omit m in
/-- The full old closing residual factors through the actual fourth node substitutions. -/
theorem arithmeticFourthClosing_factorization (b : Bool) :
    arithmeticThirdClosingEquiv hπ data H j hj u hu 4 b =
      (twoBranchCorrectionRebasedPunctureFactor R π 4
        (arithmeticThirdTerminalSmoothing hπ data H j hj u hu 4) T b).trans
        (arithmeticFourthLastEdgeEquiv hπ data H j hj u hu 4 b true) := by
  have hout := arithmeticFourthLastLayerField_outgoing hπ data H j hj u hu b
  dsimp only at hout
  rw [arithmeticFourthLastEdgeEquiv, arithmeticFourthTerminalPuncture_fourth,
    arithmeticFourthLastPuncture_fourth,
    hout]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFourthResidualField_subst hπ data H j hj u hu .closing b
  change (arithmeticThirdClosingEquiv hπ data H j hj u hu 4 b).toAlgHom = _ at h
  rw [h]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (reciprocalField (nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (parts_add (arithmeticFourthResidualField hπ data H j hj u hu .closing b)).symm.trans
    (add_comm _ _)

omit m in
/-- Both closing residuals vanish as complete Laurent maps on the fourth layer. -/
theorem arithmeticFourthClosingEquiv_fourth (b : Bool) :
    arithmeticFourthClosingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthClosingEquiv
  rw [arithmeticFourthClosing_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
