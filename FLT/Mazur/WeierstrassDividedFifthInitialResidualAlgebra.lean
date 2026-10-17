/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialLayerFields
public import FLT.Mazur.WeierstrassDividedFifthShallowPunctureIdentification
public import FLT.Mazur.WeierstrassDividedFifthInitialNodes

/-!
# Full fifth residuals from the actual whole-node puncture factors

The depth-one edges use the same shared node corrections and the exact
old smoothing at each endpoint. Both closing residuals vanish at stage five.
These algebra maps still require installation in the depth-one fifth global atlas.
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
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthTerminalSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthInitialLastIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthInitialNeighborIntegralField hπ data H j hj u hu
local notation "T" => arithmeticFifthShallowTerminalIntegralField hπ data H j hj u hu
/-- Both last-node substitutions expressed in the original inverse edge coordinates. -/
def arithmeticFifthInitialLastEdgeEquiv (b a : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m τ (V b) a)).trans invert

/-- The full closing residual after both actual fifth endpoint substitutions. -/
def arithmeticFifthInitialClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionRebasedPunctureFactor R π m t T b).symm.trans
      (arithmeticFourthClosingEquiv hπ data H j hj u hu m b)).trans
    (arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu m b true).symm

/-- The shared incoming residual uses the same last-node factor as the closing edge. -/
def arithmeticFifthInitialIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu m b false).trans
      (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

omit m in
/-- The full old closing residual factors through the actual fifth node substitutions. -/
theorem arithmeticFifthInitialClosing_factorization (b : Bool) :
    arithmeticFourthClosingEquiv hπ data H j hj u hu 5 b =
      (twoBranchCorrectionRebasedPunctureFactor R π 5
        (arithmeticFourthTerminalSmoothing hπ data H j hj u hu 5) T b).trans
        (arithmeticFifthInitialLastEdgeEquiv hπ data H j hj u hu 5 b true) := by
  have hout := arithmeticFifthInitialLastLayerField_outgoing hπ data H j hj u hu b
  dsimp only at hout
  rw [arithmeticFifthInitialLastEdgeEquiv, arithmeticFifthShallowTerminalPuncture_fifth,
    arithmeticFifthInitialLastPuncture_fifth,
    hout]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .closing b
  change (arithmeticFourthClosingEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
  rw [h]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (reciprocalField (nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal, reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (parts_add (arithmeticFifthResidualField hπ data H j hj u hu .closing b)).symm.trans
    (add_comm _ _)

omit m in
/-- Both closing residuals vanish as complete Laurent maps on the fifth layer. -/
theorem arithmeticFifthInitialClosingEquiv_fifth (b : Bool) :
    arithmeticFifthInitialClosingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  unfold arithmeticFifthInitialClosingEquiv
  rw [arithmeticFifthInitialClosing_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
