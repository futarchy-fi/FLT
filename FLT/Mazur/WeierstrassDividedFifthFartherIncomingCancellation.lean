/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodes
public import FLT.Mazur.WeierstrassDividedFifthDeepCancellation

/-!
# The shared outgoing edge of the depth-three initial neighbor

The specialized farther factor keeps its outgoing field, so the outer incoming
edge and the original initial edge can be corrected by the same whole node.
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

local notation "t" => arithmeticFifthDeepInput hπ data H j hj u hu

/-- The outer incoming edge uses the specialized farther node's full outgoing puncture. -/
def arithmeticFifthFartherIncomingEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  ((arithmeticFifthPairedEdgeEquiv hπ data H j hj u hu
      .outerPreceding .outerIncoming m (t .outer m b) b).trans
        (arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu m b)).trans
    (twoBranchCorrectionPunctureFactor R π m (s b) (P b) true).symm

omit m in
/-- Changing the opposite initial field preserves complete cancellation of the shared edge. -/
theorem arithmeticFifthFartherIncomingEquiv_fifth (b : Bool) :
    arithmeticFifthFartherIncomingEquiv hπ data H j hj u hu 5 b = AlgEquiv.refl := by
  have h := arithmeticFifthDeepOuterIncomingEquiv_fifth hπ data H j hj u hu b
  unfold arithmeticFifthFartherIncomingEquiv
  unfold arithmeticFifthDeepOuterIncomingEquiv at h
  rw [arithmeticFifthFartherNeighborPuncture_fifth,
    arithmeticFifthFartherNeighborField_outgoing, correctionField_positive,
    arithmeticFifthResidualIntegralField_spec]
  rw [arithmeticFifthDeepPuncture_fifth, arithmeticFifthPairedField_outgoing,
    fifthDeepOutgoing] at h
  exact h

end FLT.Mazur.WeierstrassDividedDepth
