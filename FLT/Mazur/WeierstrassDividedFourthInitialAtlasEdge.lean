/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialIdentification
public import FLT.Mazur.WeierstrassDividedFourthInitialCancellation

/-!
# The installed fourth initial edge retains its full base parameter

The actual global overlap has the complete algebraic residual. Its fourth
layer cancels to the original Mobius/right parameter on both initial labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialAtlasChart arithmeticThirdInitialAtlasChart
  arithmeticFourthInitialIso arithmeticFourthInitialNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha : 1 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticFourthInitialIdentification hπ data H m j hj u hu ha
local notation "J₃" => arithmeticThirdInitialIdentification hπ data H m j hj u hu ha
local notation "M" => arithmeticFourthInitialNeighborIdentification hπ data H m j hj u hu ha
local notation "M₃" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m
local notation "s₃" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthInitialNeighborIntegralField hπ data H j hj u hu

/-- The installed depth-one initial edge has exactly the complete fourth residual. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_residual_initial (b : Bool) :
    arithmeticFourthInitialPuncture hπ data H m j hj u hu b ≫ (J b).hom ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticFourthInitialEquiv hπ data H j hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFourthInitialPuncture, Category.assoc, arithmeticFourthInitial_chart]
  rw [arithmeticThirdInitialAtlas_residual_initial hπ data H m j hj u hu ha b]
  simp only [arithmeticFourthInitialEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, arithmeticThirdInitialEquiv_spec]
  have h := arithmeticFourthInitialNeighborIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticFourthInitialNeighbor_chart]

omit m in
/-- Both actual initial overlaps reduce to their full original base at layer four. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_initial_fourth (b : Bool) :
    arithmeticFourthInitialPuncture hπ data H 4 j hj u hu b ≫
      (arithmeticFourthInitialIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 4 j hj)).hom ≫
        rightBranchOpen (Quotient R π 4)
          (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu 4 b) ≫
        (arithmeticFourthInitialNeighborIdentification hπ data H 4 j hj u hu ha b).hom ≫
          arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticFourthInitialAtlas_residual_initial, arithmeticFourthInitialEquiv_fourth]

end FLT.Mazur.WeierstrassDividedDepth
