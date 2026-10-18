/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFiniteAtlas
public import FLT.Mazur.WeierstrassDividedZeroFifthAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroFiniteResiduals

/-!
# The actual finite initial overlap retains the original base parameter

Both initial labels use their full finite open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteAtlasChart arithmeticZeroFifthAtlasChart
  arithmeticZeroFiniteInitialIso arithmeticZeroFiniteLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (k m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu
local notation "κ" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu
local notation "s" => PolygonArithmeticSimultaneous.State.last
  (arithmeticZeroFiniteState hπ data H 0 hj u hu k) m

/-- The installed initial overlap is exactly the full finite algebraic residual. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_residual_initial (b : Bool) :
    arithmeticZeroFiniteInitialPuncture hπ data H k m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).initialEquiv m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  have hi := arithmeticZeroFiniteAtlasCorrection_chart hπ data H k m hj u hu (.initial b)
  change (arithmeticZeroFiniteInitialIso hπ data H k m 0 hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticZeroFiniteInitialPuncture, Category.assoc, hi]
  rw [arithmeticZeroFifthAtlas_residual_initial]
  simp only [arithmeticZeroFiniteState_initialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroFiniteLastIso_puncture hπ data H k m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    show (arithmeticZeroFiniteLastIso hπ data H k m 0 hj u hu b).hom ≫
      ι (.retained ⟨0, by omega⟩ b) = κ (.retained ⟨0, by omega⟩ b) from
        arithmeticZeroFiniteAtlasCorrection_chart hπ data H k m hj u hu _]

/-- The installed finite initial overlaps equal the full base on every attained quotient. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_initial_normalized
    (hm : m ≤ 5 + k) (b : Bool) :
    arithmeticZeroFiniteInitialPuncture hπ data H k m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H m 0 hj)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroFiniteAtlas_residual_initial,
    (arithmeticZeroFiniteState_normalized_le hπ data H 0 hj u hu k m hm).1 b]

end FLT.Mazur.WeierstrassDividedDepth
