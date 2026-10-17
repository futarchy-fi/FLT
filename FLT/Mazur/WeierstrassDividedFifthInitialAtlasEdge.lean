/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasEdge
public import FLT.Mazur.WeierstrassDividedFifthInitialCancellation

/-!
# The actual fifth initial overlap retains the original base parameter

Both initial labels use their full fifth open and the same neighboring factor
as the preceding edge. Cancellation preserves the complete Mobius/right base.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialAtlasChart arithmeticFourthInitialAtlasChart
  arithmeticFifthInitialIso arithmeticFifthInitialNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu
local notation "s" => arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m
local notation "s₄" => arithmeticFourthInitialNeighborSmoothing hπ data H 1 hj u hu m

/-- The installed initial overlap is exactly the full fifth algebraic residual. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_residual_initial (b : Bool) :
    arithmeticFifthInitialPuncture hπ data H m 1 hj u hu b ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticFifthInitialEquiv hπ data H 1 hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFifthInitialPuncture, Category.assoc, arithmeticFifthInitialInitial_chart]
  rw [arithmeticFourthInitialAtlas_residual_initial]
  simp only [arithmeticFifthInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have h := arithmeticFifthInitialNeighborIso_puncture hπ data H m 1 hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticFifthInitialNeighbor_chart]

omit m in
/-- The actual initial edges reduce to their full original base on the fifth layer. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_initial_fifth (b : Bool) :
    arithmeticFifthInitialPuncture hπ data H 5 1 hj u hu b ≫
      arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 5 1 hj)).hom ≫
        rightBranchOpen (Quotient R π 5)
          (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu 5 b) ≫
          arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticFifthInitialAtlas_residual_initial, arithmeticFifthInitialEquiv_fifth]

end FLT.Mazur.WeierstrassDividedDepth
