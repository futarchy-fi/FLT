/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticRetainedChainFiniteResiduals
public import FLT.Mazur.WeierstrassDividedOneFiniteNodes

/-!
# Complete finite depth-one residual formulas

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
  (H : ArithmeticAtlasCoefficients data) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => fun m ↦ arithmeticInitialBaseEquiv data H m 1 hj
local notation "S" => arithmeticOneSeedState hπ data H hj u hu
local notation "hS" => arithmeticOneSeedState_compatible hπ data H hj u hu
local notation "ha" => arithmeticOneSeedState_annihilated hπ data H hj u hu
local notation "hr" => arithmeticOneSeedState_normalized hπ data H hj u hu
local notation "hB" => fun m ↦ arithmeticInitialBaseEquiv_restriction data H m 1 hj
local notation "hb" => fun m ↦ arithmeticInitialBaseEquiv_symm_sub_mem data H m 1 hj
local notation "I" => arithmeticOneFiniteState hπ data H hj u hu
variable (k m : ℕ)
local notation "Q" => Quotient R π m

/-- The full outgoing substitution of either node in inverse-left coordinates. -/
def arithmeticOneFiniteOutgoingEquiv (i : Fin 2) (b : Bool) : Q[T;T⁻¹] ≃ₐ[Q] Q[T;T⁻¹] :=
  (LaurentPolynomial.invert.trans
    (arithmeticOneFiniteRetainedPunctureEquiv hπ data H hj u hu k m i b true)).trans
      LaurentPolynomial.invert

/-- The initial residual keeps the full seed base and the first retained node's factor. -/
theorem arithmeticOneFiniteState_initialEquiv (b : Bool) :
    (I k).edgeEquiv .initial m b =
      ((arithmeticOneFiniteRetainedPunctureEquiv hπ data H hj u hu k m 0 b false).trans
        (arithmeticFifthInitialEquiv hπ data H 1 hj u hu m b)).trans
          (arithmeticOneFiniteInitialPunctureEquiv hπ data H hj u hu k m b true).symm :=
  (S).iterate_initialEquiv B hB hb hS ha 5 hr m b k

/-- The internal residual keeps both whole-node factors and its conjugated seed overlap. -/
theorem arithmeticOneFiniteState_incomingEquiv (b : Bool) :
    (I k).edgeEquiv (.incoming 0) m b =
      ((arithmeticOneFiniteRetainedPunctureEquiv hπ data H hj u hu k m 1 b false).trans
        (arithmeticOneSeedIncoming hπ data H hj u hu m b)).trans
          (arithmeticOneFiniteOutgoingEquiv hπ data H hj u hu k m 0 b).symm :=
  (S).iterate_incomingEquiv B hB hb hS ha 5 hr m 0 b k

/-- The closing residual uses the same last-node factor and common terminal. -/
theorem arithmeticOneFiniteState_closingEquiv (b : Bool) :
    (I k).edgeEquiv .closing m b =
      ((arithmeticOneFiniteTerminalPunctureEquiv hπ data H hj u hu k m b).symm.trans
        (arithmeticFifthInitialClosingEquiv hπ data H 1 hj u hu m b)).trans
          (arithmeticOneFiniteOutgoingEquiv hπ data H hj u hu k m 1 b).symm :=
  (S).iterate_closingEquiv B hB hb hS ha 5 hr m b k

end FLT.Mazur.WeierstrassDividedDepth
