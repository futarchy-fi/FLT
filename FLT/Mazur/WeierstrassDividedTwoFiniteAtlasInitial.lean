/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTwoFiniteAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasEdge
public import FLT.Mazur.WeierstrassDividedTwoFiniteResiduals

/-!
# The actual finite initial overlap retains the original base parameter

Both initial labels use their full finite open and the same first-node factor
as the internal edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticTwoFiniteAtlasChart arithmeticFifthShallowAtlasChart
  arithmeticTwoFiniteInitialIso arithmeticTwoFiniteRetainedIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticTwoFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticTwoFiniteState hπ data H hj u hu k) m 0

/-- The installed initial overlap is exactly the full finite algebraic residual. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_residual_initial (b : Bool) :
    arithmeticTwoFiniteInitialPuncture hπ data H k m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso
        ((arithmeticTwoFiniteState hπ data H hj u hu k).edgeEquiv .initial m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained (0 : Fin 3) b) := by
  have hi := arithmeticTwoFiniteAtlasCorrection_chart hπ data H k m hj u hu (.initial b)
  change (arithmeticTwoFiniteInitialIso hπ data H k m hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticTwoFiniteInitialPuncture, Category.assoc, hi]
  rw [arithmeticFifthShallowAtlas_residual_initial]
  simp only [arithmeticTwoFiniteState_initialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticTwoFiniteRetainedIso_puncture hπ data H k m hj u hu 0 b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticTwoFiniteFirst_chart]
  rfl

/-- The installed finite initial overlaps equal the full base on every attained quotient. -/
@[reassoc] theorem arithmeticTwoFiniteAtlas_initial_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    arithmeticTwoFiniteInitialPuncture hπ data H k m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 2 hj)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained (0 : Fin 3) b) := by
  rw [arithmeticTwoFiniteAtlas_residual_initial,
    (arithmeticTwoFiniteState_normalized hπ data H hj u hu k m hm) .initial b,
    PolygonArithmeticRetainedChain.edgeBase]

end FLT.Mazur.WeierstrassDividedDepth
