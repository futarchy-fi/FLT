/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFiniteResiduals
public import FLT.Mazur.WeierstrassDividedThreeFiniteNodes

/-!
# Complete finite depth-three residual formulas

Specialize the constructed finite factors to the proved fifth seed. Each
comparison retains its exact source and target smoothing and both punctures.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonArithmeticRetainedChain PolygonSmoothing
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (hj : 4 ≤ n)
  (u : Rˣ) (hu : (data ⟨4, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 3 hj
local notation "S" => arithmeticThreeSeedState hπ data H hj u hu
local notation "hS" => arithmeticThreeSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticThreeSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticThreeSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 3 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 3 hj
local notation "I" => arithmeticThreeFiniteState hπ data H hj u hu
variable (k m : ℕ)
local notation "Q" => Quotient R π m

/-- The full outgoing substitution of either node in inverse-left coordinates. -/
def arithmeticThreeFiniteOutgoingEquiv (i : Fin 4) (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (arithmeticThreeFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b true)).trans
      LaurentPolynomial.invert

/-- The initial residual keeps the full seed base and the first retained node's factor. -/
theorem arithmeticThreeFiniteState_initialEquiv (b : Bool) :
    (I k).edgeEquiv .initial m b =
      ((arithmeticThreeFiniteRetainedPunctureEquiv hπ data H hj u hu k m 0 b false).trans
        (arithmeticFifthFartherEquiv hπ data H 3 hj u hu m b)).trans
          (arithmeticThreeFiniteInitialPunctureEquiv hπ data H hj u hu k m b true).symm :=
  (S).iterate_initialEquiv B hB hb hS ha 5 hr m b k

/-- The internal residual keeps both whole-node factors and its conjugated seed overlap. -/
theorem arithmeticThreeFiniteState_incomingEquiv (i : Fin 3) (b : Bool) :
    (I k).edgeEquiv (.incoming i) m b =
      ((arithmeticThreeFiniteRetainedPunctureEquiv hπ data H hj u hu k m i.succ b false).trans
        (arithmeticThreeSeedIncoming hπ data H hj u hu m i b)).trans
          (arithmeticThreeFiniteOutgoingEquiv hπ data H hj u hu k m i.castSucc b).symm :=
  (S).iterate_incomingEquiv B hB hb hS ha 5 hr m i b k

/-- The closing residual uses the same last-node factor and common terminal. -/
theorem arithmeticThreeFiniteState_closingEquiv (b : Bool) :
    (I k).edgeEquiv .closing m b =
      ((arithmeticThreeFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).symm.trans
        (arithmeticFifthShallowClosingEquiv hπ data H 3 hj u hu m b)).trans
          (arithmeticThreeFiniteOutgoingEquiv hπ data H hj u hu k m 3 b).symm :=
  (S).iterate_closingEquiv B hB hb hS ha 5 hr m b k

end FLT.Mazur.WeierstrassDividedDepth
