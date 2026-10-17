/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherIdentification
public import FLT.Mazur.WeierstrassDividedFifthFartherCancellation

/-!
# The installed fifth initial edge retains its full base parameter

The actual global overlap has the complete algebraic residual. Its fifth
layer cancels to the original Mobius/right parameter on both initial labels.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthFartherAtlasChart arithmeticFourthOuterAtlasChart
  arithmeticFifthFartherIso arithmeticFifthFartherNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha : 3 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthFartherAtlasChart hπ data H m j hj u hu ha
local notation "κ" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticFifthFartherIdentification hπ data H m j hj u hu ha
local notation "J₃" => arithmeticFourthOuterInitialThreeIdentification hπ data H m j hj u hu ha
local notation "M" => arithmeticFifthFartherNeighborIdentification hπ data H m j hj u hu ha
local notation "M₃" => arithmeticFourthFartherIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m
local notation "s₃" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthFartherIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthFartherNeighborIntegralField hπ data H j hj u hu

/-- The installed depth-three initial edge has exactly the complete fifth residual. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_residual_initial (b : Bool) :
    arithmeticFifthFartherPuncture hπ data H m j hj u hu b ≫ (J b).hom ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticFifthFartherEquiv hπ data H j hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFifthFartherPuncture, Category.assoc, arithmeticFifthFarther_chart]
  rw [arithmeticFourthOuterAtlas_farther_initial hπ data H m j hj u hu ha b,
    arithmeticInitialNormalizedPunctureIso_inv_comp_assoc]
  simp only [arithmeticFifthFartherEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, arithmeticInitialBaseEquiv_spec,
    arithmeticFourthFartherOppositeEquiv]
  have h := arithmeticFifthFartherNeighborIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticFifthFartherNeighbor_chart]

omit m in
/-- Both actual initial overlaps reduce to their full original base at layer five. -/
@[reassoc] theorem arithmeticFifthFartherAtlas_initial_fifth (b : Bool) :
    arithmeticFifthFartherPuncture hπ data H 5 j hj u hu b ≫
      (arithmeticFifthFartherIdentification hπ data H 5 j hj u hu ha b).hom ≫
        arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 5 j hj)).hom ≫
        rightBranchOpen (Quotient R π 5)
          (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu 5 b) ≫
        (arithmeticFifthFartherNeighborIdentification hπ data H 5 j hj u hu ha b).hom ≫
          arithmeticFifthFartherAtlasChart hπ data H 5 j hj u hu ha
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticFifthFartherAtlas_residual_initial, arithmeticFifthFartherEquiv_fifth]

end FLT.Mazur.WeierstrassDividedDepth
