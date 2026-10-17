/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondAtlas
public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroSecondCancellation

/-!
# The actual second initial overlap retains the original base parameter

Both initial labels use their full second open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroSecondAtlasChart arithmeticZeroFirstAtlasChart
  arithmeticZeroSecondInitialIso arithmeticZeroSecondLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu m

/-- The installed initial overlap is exactly the full second algebraic residual. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_residual_initial (b : Bool) :
    arithmeticZeroSecondInitialPuncture hπ data H m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticZeroSecondInitialEquiv hπ data H 0 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  have hi := arithmeticZeroSecondAtlasCorrection_chart hπ data H m hj u hu (.initial b)
  change (arithmeticZeroSecondInitialIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticZeroSecondInitialPuncture, Category.assoc, hi]
  rw [arithmeticZeroFirstAtlas_residual_initial]
  simp only [arithmeticZeroSecondInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroSecondLastIso_puncture hπ data H m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    show (arithmeticZeroSecondLastIso hπ data H m 0 hj u hu b).hom ≫
      ι (.retained ⟨0, by omega⟩ b) = κ (.retained ⟨0, by omega⟩ b) from
        arithmeticZeroSecondAtlasCorrection_chart hπ data H m hj u hu _]

omit m in
/-- The actual initial edges reduce to their full original base on the second layer. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_initial_second (b : Bool) :
    arithmeticZeroSecondInitialPuncture hπ data H 2 0 hj u hu b ≫
      arithmeticZeroSecondAtlasChart hπ data H 2 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 2 0 hj)).hom ≫
        rightBranchOpen (Quotient R π 2)
          (arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu 2 b) ≫
          arithmeticZeroSecondAtlasChart hπ data H 2 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroSecondAtlas_residual_initial, arithmeticZeroSecondInitialEquiv_second]

end FLT.Mazur.WeierstrassDividedDepth
