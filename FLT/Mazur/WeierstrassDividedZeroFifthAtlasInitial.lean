/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthAtlas
public import FLT.Mazur.WeierstrassDividedZeroFourthAtlasInitial
public import FLT.Mazur.WeierstrassDividedZeroFifthCancellation

/-!
# The actual fifth initial overlap retains the original base parameter

Both initial labels use their full fifth open and the same last-node factor
as the closing edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFifthAtlasChart arithmeticZeroFourthAtlasChart
  arithmeticZeroFifthInitialIso arithmeticZeroFifthLastIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticZeroFifthAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticZeroFourthAtlasChart hπ data H m hj u hu
local notation "s" => arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu m

/-- The installed initial overlap is exactly the full fifth algebraic residual. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_residual_initial (b : Bool) :
    arithmeticZeroFifthInitialPuncture hπ data H m 0 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticZeroFifthInitialEquiv hπ data H 0 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  have hi := arithmeticZeroFifthAtlasCorrection_chart hπ data H m hj u hu (.initial b)
  change (arithmeticZeroFifthInitialIso hπ data H m 0 hj u hu b).hom ≫ _ = _ at hi
  simp only [arithmeticZeroFifthInitialPuncture, Category.assoc, hi]
  rw [arithmeticZeroFourthAtlas_residual_initial]
  simp only [arithmeticZeroFifthInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticZeroFifthLastIso_puncture hπ data H m 0 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    show (arithmeticZeroFifthLastIso hπ data H m 0 hj u hu b).hom ≫
      ι (.retained ⟨0, by omega⟩ b) = κ (.retained ⟨0, by omega⟩ b) from
        arithmeticZeroFifthAtlasCorrection_chart hπ data H m hj u hu _]

omit m in
/-- The actual initial edges reduce to their full original base on the fifth layer. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_initial_fifth (b : Bool) :
    arithmeticZeroFifthInitialPuncture hπ data H 5 0 hj u hu b ≫
      arithmeticZeroFifthAtlasChart hπ data H 5 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 5 0 hj)).hom ≫
        rightBranchOpen (Quotient R π 5)
          (arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu 5 b) ≫
          arithmeticZeroFifthAtlasChart hπ data H 5 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticZeroFifthAtlas_residual_initial, arithmeticZeroFifthInitialEquiv_fifth]

end FLT.Mazur.WeierstrassDividedDepth
