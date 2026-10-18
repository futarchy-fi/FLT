/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoSeedState
public import FLT.Mazur.PolygonArithmeticRetainedChainDiagonal

/-!
# Finite and diagonal induction from the oriented depth-two seed

Every later field is selected from the actual preceding state. The complete
initial base and common terminal persist through all correction rounds.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 2 hj
local notation "S" => arithmeticTwoSeedState hπ data H hj u hu
local notation "hS" => arithmeticTwoSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticTwoSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticTwoSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 2 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 2 hj
/-- Any finite number of further rounds from the actual normalized fifth packet. -/
def arithmeticTwoFiniteState (k : ℕ) : State R π 2 :=
  (S).iterate B hB hb hS ha 5 hr k

/-- The finite chain retains all coefficient squares. -/
theorem arithmeticTwoFiniteState_compatible (k : ℕ) :
    (arithmeticTwoFiniteState hπ data H hj u hu k).Compatible :=
  (S).iterate_compatible B hB hb hS ha 5 hr k

/-- Every accumulated finite drift retains its arithmetic annihilator. -/
theorem arithmeticTwoFiniteState_annihilated (k : ℕ) :
    (arithmeticTwoFiniteState hπ data H hj u hu k).Annihilated :=
  (S).iterate_annihilated B hB hb hS ha 5 hr k

/-- Every finite edge is normalized at every attained arithmetic order. -/
theorem arithmeticTwoFiniteState_normalized (k m : ℕ) (hm : m ≤ 5 + k) :
    (arithmeticTwoFiniteState hπ data H hj u hu k).Normalized B m :=
  (S).iterate_normalized_le B hB hb hS ha 5 hr k m hm

/-- The diagonal uses m further rounds on quotient m. -/
def arithmeticTwoDiagonalState : State R π 2 := (S).diagonal B hB hb hS ha 5 hr

/-- Stabilization retains the full diagonal coefficient squares. -/
theorem arithmeticTwoDiagonalState_compatible :
    (arithmeticTwoDiagonalState hπ data H hj u hu).Compatible :=
  (S).diagonal_compatible B hB hb hS ha 5 hr

/-- The complete diagonal smoothings retain their annihilators. -/
theorem arithmeticTwoDiagonalState_annihilated :
    (arithmeticTwoDiagonalState hπ data H hj u hu).Annihilated :=
  (S).diagonal_annihilated B hB hb hS ha 5 hr

/-- Every complete diagonal edge is normalized at every arithmetic order. -/
theorem arithmeticTwoDiagonalState_normalized (m : ℕ) :
    (arithmeticTwoDiagonalState hπ data H hj u hu).Normalized B m :=
  (S).diagonal_normalized B hB hb hS ha 5 hr m

end FLT.Mazur.WeierstrassDividedDepth
