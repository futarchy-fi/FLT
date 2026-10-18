/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdAtlas
public import FLT.Mazur.WeierstrassDividedZeroSecondAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroThirdCancellation

/-!
# The actual third initial overlap retains the original base parameter

Both initial labels use their full third open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroThirdAtlasChart arithmeticZeroSecondAtlasChart
  arithmeticZeroThirdInitialIso arithmeticZeroThirdLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroThirdAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroSecondAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu m

/-- The installed initial overlap is exactly the full third algebraic residual. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_residual_initial (b : Bool) :
    arithmeticZeroThirdInitialPuncture hπ data H m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticZeroThirdInitialEquiv hπ data H 0 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  have hi := arithmeticZeroThirdAtlasCorrection_chart hπ data H m hj u hu (.initial b)
  change (arithmeticZeroThirdInitialIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticZeroThirdInitialPuncture, Category.assoc, hi]
  rw [arithmeticZeroSecondAtlas_residual_initial]
  simp only [arithmeticZeroThirdInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroThirdLastIso_puncture hπ data H m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    show (arithmeticZeroThirdLastIso hπ data H m 0 hj u hu b).hom ≫
      ι (.retained ⟨0, by omega⟩ b) = κ (.retained ⟨0, by omega⟩ b) from
        arithmeticZeroThirdAtlasCorrection_chart hπ data H m hj u hu _]

omit m in
/-- The actual initial edges reduce to their full original base on the third layer. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_initial_third (b : Bool) :
    arithmeticZeroThirdInitialPuncture hπ data H 3 0 hj u hu b ≫
      arithmeticZeroThirdAtlasChart hπ data H 3 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 3 0 hj)).hom ≫
        rightBranchOpen (Quotient R π 3)
          (arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu 3 b) ≫
          arithmeticZeroThirdAtlasChart hπ data H 3 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroThirdAtlas_residual_initial, arithmeticZeroThirdInitialEquiv_third]

end FLT.Mazur.WeierstrassDividedDepth
