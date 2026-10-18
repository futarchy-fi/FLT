/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdPunctures
public import FLT.Mazur.PolygonArithmeticLaurentIdentityRestriction
public import FLT.Mazur.WeierstrassDividedZeroSecondResidualRestriction

/-!
# Simultaneous third cancellation at depth zero

Use the actual second smoothings on both edges of the same last node.
The initial residual returns to its full original base, and both closing
residuals vanish with a single common terminal correction.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing LaurentPolynomial WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (m : ℕ)
local notation "Q" => Quotient R π m
local notation "a" => arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticZeroThirdInitialIntegralField hπ data H j hj u hu
local notation "V" => arithmeticZeroThirdLastIntegralField hπ data H j hj u hu
local notation "T" => arithmeticZeroThirdTerminalIntegralField hπ data H j hj u hu

/-- The full initial residual after the two actual endpoint factors. -/
def arithmeticZeroThirdInitialEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionPunctureFactor R π m (s b) (V b) false).trans
      (arithmeticZeroSecondInitialEquiv hπ data H j hj u hu m b)).trans
    (correctionPunctureFactor R π m (a b) (A b) true).symm

/-- Use the outgoing puncture of that same last factor in the closing coordinate. -/
def arithmeticZeroThirdLastEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (invert.trans (twoBranchCorrectionPunctureFactor R π m (s b) (V b) true)).trans invert

/-- Correct the full previous common terminal and the new shared last factor together. -/
def arithmeticZeroThirdClosingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionRebasedPunctureFactor R π m t T b).symm.trans
      (arithmeticZeroSecondClosingEquiv hπ data H j hj u hu m b)).trans
    (arithmeticZeroThirdLastEdgeEquiv hπ data H j hj u hu m b).symm

omit m in
/-- The complete initial edge equals its full original base at the third layer. -/
theorem arithmeticZeroThirdInitialEquiv_third (b : Bool) :
    arithmeticZeroThirdInitialEquiv hπ data H j hj u hu 3 b =
      arithmeticInitialBaseEquiv data H 3 j hj := by
  unfold arithmeticZeroThirdInitialEquiv
  rw [arithmeticZeroThirdInitialPuncture_third, arithmeticZeroThirdLastPuncture_third,
    arithmeticZeroThirdLastField_incoming_spec]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π 3) 3
    (nextCorrectionParameter_square R π 2)
  · exact arithmeticInitialBaseEquiv_symm_sub_mem data H 3 j hj
  · change ((Ideal.span {parameter R π 3}).map (algebraMap _ _)) ^ 4 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 3,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    exact arithmeticZeroThirdField_subst hπ data H j hj u hu false b

omit m in
/-- The complete old closing residual factors through the two actual third corrections. -/
theorem arithmeticZeroThirdClosing_factorization (b : Bool) :
    arithmeticZeroSecondClosingEquiv hπ data H j hj u hu 3 b =
      (twoBranchCorrectionRebasedPunctureFactor R π 3
        (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu 3) T b).trans
        (arithmeticZeroThirdLastEdgeEquiv hπ data H j hj u hu 3 b) := by
  rw [arithmeticZeroThirdLastEdgeEquiv, arithmeticZeroThirdTerminalPuncture_third,
    arithmeticZeroThirdLastPuncture_third, arithmeticZeroThirdLastField_outgoing_spec]
  apply AlgEquiv.coe_toAlgHom_injective
  have h := arithmeticZeroThirdField_subst hπ data H j hj u hu true b
  change (arithmeticZeroSecondClosingEquiv hπ data H j hj u hu 3 b).toAlgHom = _ at h
  rw [h]
  change _ = (invert.toAlgHom.comp ((LaurentSquareZeroAutomorphism.subst _ _
    (LaurentBoundaryVectorField.reciprocalField
      (LaurentBoundaryCorrectionSplit.nonpositivePart _))).comp invert.toAlgHom)).comp
      (LaurentSquareZeroAutomorphism.subst _ _ (LaurentBoundaryCorrectionSplit.positivePart _))
  rw [LaurentSquareZeroAutomorphism.subst_reciprocal,
    LaurentBoundaryCorrectionSplit.reciprocalField_involutive,
    LaurentSquareZeroAutomorphism.subst_comp]
  congr 1
  exact (LaurentBoundaryCorrectionSplit.parts_add
    (arithmeticZeroThirdField hπ data H j hj u hu true b)).symm.trans (add_comm _ _)

omit m in
/-- Both closing edges vanish with the same last factor and common terminal at layer three. -/
theorem arithmeticZeroThirdClosingEquiv_third (b : Bool) :
    arithmeticZeroThirdClosingEquiv hπ data H j hj u hu 3 b = AlgEquiv.refl := by
  unfold arithmeticZeroThirdClosingEquiv
  rw [arithmeticZeroThirdClosing_factorization]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
