/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodes
public import FLT.Mazur.WeierstrassDividedFifthDeepCancellation

/-!
# Fifth cancellation relative to the full original initial parameter

The depth-three endpoint fields cancel the entire old initial residual at layer
five. The farther neighbor retains its shared outgoing correction.
These factors still need installation in the depth-three global atlas.
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
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "e" => fun (_ : Bool) ↦
  arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => arithmeticFifthFartherIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthFartherNeighborIntegralField hπ data H j hj u hu

/-- The complete corrected initial residual retains its entire previous base substitution. -/
def arithmeticFifthFartherEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((twoBranchCorrectionPunctureFactor R π m (s b) (P b) false).trans
      ((arithmeticFourthFartherOppositeEquiv hπ data H j hj u hu m b).trans
        (arithmeticInitialBaseEquiv data H m j hj))).trans
    (correctionPunctureFactor R π m (e b) (A b) true).symm

omit m in
/-- Both complete initial residuals equal their full original base at layer five. -/
theorem arithmeticFifthFartherEquiv_fifth (b : Bool) :
    arithmeticFifthFartherEquiv hπ data H j hj u hu 5 b =
      arithmeticInitialBaseEquiv data H 5 j hj := by
  unfold arithmeticFifthFartherEquiv
  rw [arithmeticFifthFartherPuncture_fifth, arithmeticFifthFartherNeighborPuncture_fifth,
    arithmeticFifthFartherNeighborField_incoming_spec]
  apply LaurentReciprocalRelativeCorrection.cancel_relative (parameter R π 5) 5
    (nextCorrectionParameter_square R π 4)
  · exact arithmeticInitialBaseEquiv_symm_sub_mem data H 5 j hj
  · change ((Ideal.span {parameter R π 5}).map (algebraMap _ _)) ^ 6 = ⊥
    rw [← Ideal.map_pow, Ideal.span_singleton_pow, parameter_pow R π 5,
      Ideal.span_singleton_zero, Ideal.map_bot]
  · apply AlgEquiv.coe_toAlgHom_injective
    have h := arithmeticFifthResidualField_subst hπ data H j hj u hu .fartherDirect b
    change (arithmeticFourthFartherOppositeEquiv hπ data H j hj u hu 5 b).toAlgHom = _ at h
    apply AlgHom.ext
    intro z
    change (arithmeticInitialBaseEquiv data H 5 j hj).symm
      (arithmeticInitialBaseEquiv data H 5 j hj
        (arithmeticFourthFartherOppositeEquiv hπ data H j hj u hu 5 b z)) = _
    rw [AlgEquiv.symm_apply_apply]
    exact DFunLike.congr_fun h z

end FLT.Mazur.WeierstrassDividedDepth
