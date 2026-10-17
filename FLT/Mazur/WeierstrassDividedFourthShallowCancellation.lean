/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowNodes
public import FLT.Mazur.WeierstrassDividedFourthIncomingCancellation

/-!
# Fourth cancellation relative to the full original initial parameter

The depth-two endpoint fields cancel the entire old initial residual at layer
four. Its earlier neighbor's other branch still cancels the shared incoming edge.
These factors still need installation in the depth-two global atlas.
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
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "e" => fun (_ : Bool) ↦
  arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFourthShallowIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthShallowNeighborIntegralField hπ data H j hj u hu

/-- The complete corrected initial residual retains its entire previous base substitution. -/
def arithmeticFourthShallowEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionPunctureFactor R π m (s b) (P b) false).trans
      ((arithmeticThirdEarlierOppositeEquiv hπ data H j hj u hu m b).trans
        (arithmeticInitialBaseEquiv data H m j hj))).trans
    (correctionPunctureFactor R π m (e b) (A b) true).symm

/-- The same earlier neighbor factor is used at the shared interior incoming edge. -/
def arithmeticFourthShallowNeighborIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthPrecedingEdgeEquiv hπ data H j hj u hu m b).trans
      (arithmeticThirdPrecedingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

omit m in
/-- Both complete initial residuals equal their full original base at layer four. -/
theorem arithmeticFourthShallowEquiv_fourth (b : Bool) :
    arithmeticFourthShallowEquiv hπ data H j hj u hu 4 b =
      arithmeticInitialBaseEquiv data H 4 j hj := by
  unfold arithmeticFourthShallowEquiv
  rw [arithmeticFourthShallowPuncture_fourth, arithmeticFourthShallowNeighborPuncture_fourth,
    arithmeticFourthShallowNeighborField_incoming_spec]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π 4) 4
    (nextCorrectionParameter_square R π 3)
  · exact arithmeticInitialBaseEquiv_symm_sub_mem data H 4 j hj
  · change ((Ideal.span {parameter R π 4}).map (algebraMap _ _)) ^ 5 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 4,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    have h := arithmeticFourthResidualField_subst hπ data H j hj u hu .earlierDirect b
    change (arithmeticThirdEarlierOppositeEquiv hπ data H j hj u hu 4 b).toAlgHom = _ at h
    apply AlgHom.ext
    intro z
    change (arithmeticInitialBaseEquiv data H 4 j hj).symm
      (arithmeticInitialBaseEquiv data H 4 j hj
        (arithmeticThirdEarlierOppositeEquiv hπ data H j hj u hu 4 b z)) = _
    rw [AlgEquiv.symm_apply_apply]
    exact DFunLike.congr_fun h z

omit m in
/-- The depth-two choice simultaneously preserves full cancellation at the next interior edge. -/
theorem arithmeticFourthShallowNeighborIncomingEquiv_fourth (b : Bool) :
    arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthShallowNeighborIncomingEquiv
  rw [arithmeticFourthPreceding_factorization, arithmeticFourthEarlierPuncture_fourth,
    arithmeticFourthShallowNeighborPuncture_fourth, arithmeticFourthShallowNeighborField_outgoing]
  have h : correctionField R π 4 (arithmeticFourthEarlierField hπ data H j hj u hu b) =
      positivePart (arithmeticFourthResidualField hπ data H j hj u hu .preceding b) := by
    rw [arithmeticFourthEarlierField, correctionField_positive,
      arithmeticFourthResidualIntegralField_spec]
  rw [h]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
