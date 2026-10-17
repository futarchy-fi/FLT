/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterTransitions
public import FLT.Mazur.WeierstrassDividedFourthOuterIdentification

/-!
# The further incoming edge of the installed fourth outer atlas

Both actual retained labels use their complete factors. The farther node's
original orientation is retained in the comparison with the third atlas.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthPrecedingIso arithmeticFourthOuterIso arithmeticFourthOuterAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (a : ℕ) (ha : a + 3 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticFourthOuterAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticFourthOuterIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "M" => arithmeticFourthFartherIdentification hπ data H m j hj u hu a ha
local notation "N₃" => arithmeticThirdEarlierIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "M₃" => arithmeticThirdUnchangedIdentification hπ data H m j hj u hu
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthOuterSmoothing hπ data H j hj u hu m
local notation "e₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- The full further incoming residual belongs to the actual two installed labels. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthOuterIncomingResidual hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (t b) ≫ (N b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  apply (cancel_epi (punctureSpecIso (correctionPunctureFactor R π m τ (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q τ ≫ (O b).hom ≫
        (M₃ ⟨a, by omega⟩ (show a + 2 < j by omega) b).hom ≫
          κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← arithmeticFourthFartherIso_outgoing, Category.assoc, arithmeticFourthFarther_chart]
    _ = (arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (e₃ b) ≫ (N₃ b).hom ≫
          κ (.retained ⟨a + 1, by omega⟩ b) := by
      simpa only [arithmeticThirdInitialAtlasChart_retained] using
        arithmeticThirdAtlas_earlier_adjacent hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticFourthOuterIncomingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFourthOuterIso_incoming_assoc, arithmeticFourthOuter_chart]

omit m in
/-- Both full installed incoming overlaps have identity residual on the fourth layer. -/
@[reassoc] theorem arithmeticFourthOuterAtlas_incoming_fourth (b : Bool) :
    leftBranchOpen (Quotient R π 4)
        (arithmeticFourthFartherSmoothing hπ data H j hj u hu 4 b) ≫
      (arithmeticFourthFartherIdentification hπ data H 4 j hj u hu a ha b).hom ≫
        arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 4)
          (arithmeticFourthOuterSmoothing hπ data H j hj u hu 4 b) ≫
        (arithmeticFourthOuterIdentification hπ data H 4 j hj u hu (a + 1)
          (by omega) b).hom ≫
            arithmeticFourthOuterAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticFourthOuterAtlas_residual_incoming hπ data H 4 j hj u hu a ha b
  rw [← arithmeticFourthOuterIncomingEquiv_spec, arithmeticFourthOuterIncomingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
