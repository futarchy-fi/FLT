/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticSimultaneousFiniteResiduals
public import FLT.Mazur.WeierstrassDividedZeroFiniteNodes

/-!
# Complete finite depth-zero residual formulas

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
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
variable (k m : ℕ)
local notation "Q" => Quotient R π m


/-- The full finite outgoing substitution in the inverse closing coordinate. -/
def arithmeticZeroFiniteLastEdgeEquiv (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (arithmeticZeroFiniteLastPunctureEquiv hπ data H j hj u hu k m b true)).trans
      LaurentPolynomial.invert

/-- The finite initial residual keeps the entire fifth overlap and both full comparisons. -/
theorem arithmeticZeroFiniteState_initialEquiv (b : Bool) :
    (I k).initialEquiv m b =
      ((arithmeticZeroFiniteLastPunctureEquiv hπ data H j hj u hu k m b false).trans
        (arithmeticZeroFifthInitialEquiv hπ data H j hj u hu m b)).trans
          (arithmeticZeroFiniteInitialPunctureEquiv hπ data H j hj u hu k m b true).symm :=
  (S).iterate_initialEquiv B hB hb hS ha 5 hr m b k

/-- The finite closing residual retains the same last factor and the common terminal. -/
theorem arithmeticZeroFiniteState_closingEquiv (b : Bool) :
    (I k).closingEquiv m b =
      ((arithmeticZeroFiniteTerminalPunctureEquiv hπ data H j hj u hu k m b).symm.trans
        (arithmeticZeroFifthClosingEquiv hπ data H j hj u hu m b)).trans
          (arithmeticZeroFiniteLastEdgeEquiv hπ data H j hj u hu k m b).symm :=
  (S).iterate_closingEquiv B hB hb hS ha 5 hr m b k

/-- Both full residuals are normalized on each earlier arithmetic quotient. -/
theorem arithmeticZeroFiniteState_normalized_le (hm : m ≤ 5 + k) :
    (I k).Normalized B m :=
  (S).iterate_normalized_le B hB hb hS ha 5 hr k m hm

end FLT.Mazur.WeierstrassDividedDepth
