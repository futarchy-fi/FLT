/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialNodes
public import FLT.Mazur.WeierstrassDividedFourthIncomingCancellation

/-!
# Fourth cancellation relative to the full original initial parameter

The depth-one endpoint fields cancel the entire old initial residual at layer
four. Its predecessor's other branch still cancels the shared incoming edge.
These factors still need installation in the depth-one global atlas.
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
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "A" => arithmeticFourthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthInitialNeighborIntegralField hπ data H j hj u hu

/-- The complete corrected initial residual retains its entire previous base substitution. -/
def arithmeticFourthInitialEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionPunctureFactor R π m (s b) (P b) false).trans
      (arithmeticThirdInitialEquiv hπ data H j hj u hu m b)).trans
    (correctionPunctureFactor R π m (e b) (A b) true).symm

/-- The same predecessor factor is used at the shared interior incoming edge. -/
def arithmeticFourthInitialNeighborIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFourthLastEdgeEquiv hπ data H j hj u hu m b false).trans
      (arithmeticThirdIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

omit m in
/-- Both complete initial residuals equal their full original base at layer four. -/
theorem arithmeticFourthInitialEquiv_fourth (b : Bool) :
    arithmeticFourthInitialEquiv hπ data H j hj u hu 4 b =
      arithmeticInitialBaseEquiv data H 4 j hj := by
  unfold arithmeticFourthInitialEquiv
  rw [arithmeticFourthInitialPuncture_fourth, arithmeticFourthInitialNeighborPuncture_fourth,
    arithmeticFourthInitialNeighborField_incoming_spec]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π 4) 4
    (nextCorrectionParameter_square R π 3)
  · exact arithmeticInitialBaseEquiv_symm_sub_mem data H 4 j hj
  · change ((Ideal.span {parameter R π 4}).map (algebraMap _ _)) ^ 5 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 4,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    exact arithmeticFourthResidualField_subst hπ data H j hj u hu .initial b

omit m in
/-- The depth-one choice simultaneously preserves full cancellation at the next interior edge. -/
theorem arithmeticFourthInitialNeighborIncomingEquiv_fourth (b : Bool) :
    arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu 4 b = AlgEquiv.refl := by
  unfold arithmeticFourthInitialNeighborIncomingEquiv
  rw [arithmeticFourthIncoming_factorization, arithmeticFourthPrecedingPuncture_fourth,
    arithmeticFourthInitialNeighborPuncture_fourth, arithmeticFourthInitialNeighborField_outgoing]
  ext z : 1
  simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply, AlgEquiv.coe_refl, id_eq]

end FLT.Mazur.WeierstrassDividedDepth
