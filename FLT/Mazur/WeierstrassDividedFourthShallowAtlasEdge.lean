/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowIdentification
public import FLT.Mazur.WeierstrassDividedFourthShallowCancellation

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
  arithmeticFourthShallowAtlasChart arithmeticThirdInitialAtlasChart
  arithmeticFourthShallowIso arithmeticFourthShallowNeighborIso
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u) (ha : 2 = j)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "J" => arithmeticFourthShallowIdentification hπ data H m j hj u hu ha
local notation "J₃" => arithmeticThirdShallowInitialIdentification hπ data H m j hj u hu ha
local notation "M" => arithmeticFourthShallowNeighborIdentification hπ data H m j hj u hu ha
local notation "M₃" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu m
local notation "s₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthShallowIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthShallowNeighborIntegralField hπ data H j hj u hu

/-- The installed depth-two initial edge has exactly the complete fourth residual. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_residual_initial (b : Bool) :
    arithmeticFourthShallowPuncture hπ data H m j hj u hu b ≫ (J b).hom ≫ ι (.initial b) =
      (punctureSpecIso (arithmeticFourthShallowEquiv hπ data H j hj u hu m b)).hom ≫
        rightBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) := by
  simp only [arithmeticFourthShallowPuncture, Category.assoc, arithmeticFourthShallow_chart]
  rw [arithmeticThirdShallowInitial_chart,
    arithmeticThirdAtlas_earlier_initial hπ data H m j hj u hu ha b,
    arithmeticInitialNormalizedPunctureIso_inv_comp_assoc]
  simp only [arithmeticFourthShallowEquiv, punctureSpecIso_trans, punctureSpecIso_symm,
    Iso.trans_hom, Iso.symm_hom, Category.assoc, arithmeticInitialBaseEquiv_spec,
    arithmeticThirdEarlierOppositeEquiv]
  have h := arithmeticFourthShallowNeighborIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  rw [← Category.assoc _ (rightBranchOpen Q (s b)), ← h, Category.assoc,
    arithmeticFourthShallowNeighbor_chart, arithmeticThirdInitialAtlasChart_retained]

omit m in
/-- Both actual initial overlaps reduce to their full original base at layer four. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_initial_fourth (b : Bool) :
    arithmeticFourthShallowPuncture hπ data H 4 j hj u hu b ≫
      (arithmeticFourthShallowIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu (.initial b) =
      (punctureSpecIso (arithmeticInitialBaseEquiv data H 4 j hj)).hom ≫
        rightBranchOpen (Quotient R π 4)
          (arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu 4 b) ≫
        (arithmeticFourthShallowNeighborIdentification hπ data H 4 j hj u hu ha b).hom ≫
          arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu
            (.retained ⟨0, by omega⟩ b) := by
  rw [arithmeticFourthShallowAtlas_residual_initial, arithmeticFourthShallowEquiv_fourth]

end FLT.Mazur.WeierstrassDividedDepth
