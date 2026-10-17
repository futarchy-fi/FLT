/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFourthZeroResidual
public import FLT.Mazur.WeierstrassDividedZeroFirstCancellation

/-!
# The actual first initial overlap retains the original base parameter

Both initial labels use their full first open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFirstAtlasChart arithmeticFourthOuterAtlasChart
  arithmeticZeroFirstInitialIso arithmeticZeroFirstLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m 0 hj u hu
local notation "s" => arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu m
local notation "s₄" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m

/-- The installed initial overlap is exactly the full first algebraic residual. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_residual_initial (b : Bool) :
    arithmeticZeroFirstInitialPuncture hπ data H m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticZeroFirstInitialEquiv hπ data H 0 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticZeroFirstInitialPuncture, Category.assoc, arithmeticZeroFirstInitial_chart]
  rw [arithmeticFourthOuterAtlas_zero_residual hπ data H m 0 hj u hu rfl]
  simp only [arithmeticZeroFirstInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroFirstLastIso_puncture hπ data H m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticZeroFirstLast_chart]

omit m in
/-- The actual initial edges reduce to their full original base on the first layer. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_initial_first (b : Bool) :
    arithmeticZeroFirstInitialPuncture hπ data H 1 0 hj u hu b ≫
      arithmeticZeroFirstAtlasChart hπ data H 1 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 1 0 hj)).hom ≫
        rightBranchOpen (Quotient R π 1)
          (arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu 1 b) ≫
          arithmeticZeroFirstAtlasChart hπ data H 1 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroFirstAtlas_residual_initial, arithmeticZeroFirstInitialEquiv_first]

end FLT.Mazur.WeierstrassDividedDepth
