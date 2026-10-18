/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthAtlas
public import FLT.Mazur.WeierstrassDividedZeroThirdAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroFourthCancellation

/-!
# The actual fourth initial overlap retains the original base parameter

Both initial labels use their full fourth open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFourthAtlasChart arithmeticZeroThirdAtlasChart
  arithmeticZeroFourthInitialIso arithmeticZeroFourthLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu m

/-- The installed initial overlap is exactly the full fourth algebraic residual. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_residual_initial (b : Bool) :
    arithmeticZeroFourthInitialPuncture hπ data H m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticZeroFourthInitialEquiv hπ data H 0 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  have hi := arithmeticZeroFourthAtlasCorrection_chart hπ data H m hj u hu (.initial b)
  change (arithmeticZeroFourthInitialIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticZeroFourthInitialPuncture, Category.assoc, hi]
  rw [arithmeticZeroThirdAtlas_residual_initial]
  simp only [arithmeticZeroFourthInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroFourthLastIso_puncture hπ data H m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    show (arithmeticZeroFourthLastIso hπ data H m 0 hj u hu b).hom ≫
      ι (.retained ⟨0, by omega⟩ b) = κ (.retained ⟨0, by omega⟩ b) from
        arithmeticZeroFourthAtlasCorrection_chart hπ data H m hj u hu _]

omit m in
/-- The actual initial edges reduce to their full original base on the fourth layer. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_initial_fourth (b : Bool) :
    arithmeticZeroFourthInitialPuncture hπ data H 4 0 hj u hu b ≫
      arithmeticZeroFourthAtlasChart hπ data H 4 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 4 0 hj)).hom ≫
        rightBranchOpen (Quotient R π 4)
          (arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu 4 b) ≫
          arithmeticZeroFourthAtlasChart hπ data H 4 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroFourthAtlas_residual_initial, arithmeticZeroFourthInitialEquiv_fourth]

end FLT.Mazur.WeierstrassDividedDepth
