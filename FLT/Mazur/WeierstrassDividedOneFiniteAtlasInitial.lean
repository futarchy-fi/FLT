/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOneFiniteAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasEdge
public import FLT.Mazur.WeierstrassDividedOneFiniteResiduals

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
  arithmeticOneFiniteAtlasChart arithmeticFifthInitialAtlasChart
  arithmeticOneFiniteInitialIso arithmeticOneFiniteRetainedIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticOneFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticRetainedChain.State.retained
  (arithmeticOneFiniteState hπ data H hj u hu k) m 0

/-- The installed initial overlap is exactly the full finite algebraic residual. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_residual_initial (b : Bool) :
    arithmeticOneFiniteInitialPuncture hπ data H k m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso
        ((arithmeticOneFiniteState hπ data H hj u hu k).edgeEquiv .initial m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained (0 : Fin 2) b) := by
  have hi := arithmeticOneFiniteAtlasCorrection_chart hπ data H k m hj u hu (.initial b)
  change (arithmeticOneFiniteInitialIso hπ data H k m hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticOneFiniteInitialPuncture, Category.assoc, hi]
  rw [arithmeticFifthInitialAtlas_residual_initial]
  simp only [arithmeticOneFiniteState_initialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticOneFiniteRetainedIso_puncture hπ data H k m hj u hu 0 b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticOneFiniteFirst_chart]
  rfl

/-- The installed finite initial overlaps equal the full base on every attained quotient. -/
@[reassoc] theorem arithmeticOneFiniteAtlas_initial_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    arithmeticOneFiniteInitialPuncture hπ data H k m hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 1 hj)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained (0 : Fin 2) b) := by
  rw [arithmeticOneFiniteAtlas_residual_initial,
    (arithmeticOneFiniteState_normalized hπ data H hj u hu k m hm) .initial b,
    PolygonArithmeticRetainedChain.edgeBase]

end FLT.Mazur.WeierstrassDividedDepth
