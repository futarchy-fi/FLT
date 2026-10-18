/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousDiagonal
public import FLT.Mazur.WeierstrassDividedZeroFiniteState

/-!
# The actual diagonal depth-zero correction state

Choose m further measured rounds on arithmetic layer m. Stabilization proves
compatibility even though the correction count changes with arithmetic order.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticSimultaneous PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m j hj
local notation "S" => arithmeticZeroFifthState hπ data H j hj u hu
local notation "hS" => arithmeticZeroFifthState_compatible hπ data H j hj u hu
local notation "ha" => arithmeticZeroFifthState_annihilated hπ data H j hj u hu
local notation "hr" => arithmeticZeroFifthState_normalized hπ data H j hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m j hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m j hj
local notation "I" => arithmeticZeroFiniteState hπ data H j hj u hu

/-- The diagonal state specializes the full measured induction from the actual fifth seed. -/
def arithmeticZeroDiagonalState : State R π := (S).diagonal B hB hb hS ha 5 hr

local notation "D" => arithmeticZeroDiagonalState hπ data H j hj u hu

/-- Every diagonal smoothing and full residual respects the original coefficient quotients. -/
theorem arithmeticZeroDiagonalState_compatible : (D).Compatible :=
  (S).diagonal_compatible B hB hb hS ha 5 hr

/-- Every diagonal smoothing retains its actual top-power annihilator. -/
theorem arithmeticZeroDiagonalState_annihilated : (D).Annihilated :=
  (S).diagonal_annihilated B hB hb hS ha 5 hr

/-- The diagonal's complete initial and closing edges are normalized at every order. -/
theorem arithmeticZeroDiagonalState_normalized (m : ℕ) : (D).Normalized B m :=
  (S).diagonal_normalized B hB hb hS ha 5 hr m

/-- The actual diagonal initial smoothing is the finite smoothing with correction count m. -/
theorem arithmeticZeroDiagonalState_initial (m : ℕ) (b : Bool) :
    (D).initial m b = (I m).initial m b := rfl

/-- The actual diagonal shared last smoothing retains every one of its m finite drifts. -/
theorem arithmeticZeroDiagonalState_last (m : ℕ) (b : Bool) :
    (D).last m b = (I m).last m b := rfl

/-- The common diagonal terminal retains all m accumulated inverse drifts. -/
theorem arithmeticZeroDiagonalState_terminal (m : ℕ) :
    (D).terminal m = (I m).terminal m := rfl

end FLT.Mazur.WeierstrassDividedDepth
