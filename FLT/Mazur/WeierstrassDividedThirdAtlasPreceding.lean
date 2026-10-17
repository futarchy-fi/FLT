/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierGeometry
public import FLT.Mazur.WeierstrassDividedThirdIncomingCancellation

/-!
# The full third edge from an earlier retained label

For an existing earlier retained node, the algebraic preceding cancellation
is the actual global edge equation with both changed smoothings retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdPrecedingIso arithmeticThirdEarlierOrientedIso arithmeticThirdAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (a : ℕ) (ha : a + 2 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticThirdPrecedingIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "M" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu a ha
local notation "N₂" => arithmeticSecondJointPrecedingIdentification
  hπ data H m j hj u hu (a + 1) (by omega)
local notation "M₂" => arithmeticSecondJointEarlierIdentification
  hπ data H m j hj u hu
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "s₂" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "V" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu

/-- The installed preceding edge has precisely the full third Laurent residual. -/
@[reassoc] theorem arithmeticThirdAtlas_residual_preceding (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticThirdPrecedingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (t b) ≫ (N b).hom ≫ ι (.retained ⟨a + 1, by omega⟩ b) := by
  apply (cancel_epi (punctureSpecIso (correctionPunctureFactor R π m τ (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q τ ≫ (O b).hom ≫
        (M₂ ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫
        κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← arithmeticThirdEarlierOrientedIso_outgoing, Category.assoc, Category.assoc,
        arithmeticThirdEarlier_chart]
    _ = (arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s₂ b) ≫ (N₂ b).hom ≫
          κ (.retained ⟨a + 1, by omega⟩ b) :=
      arithmeticSecondJointAtlas_preceding_adjacent hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticThirdPrecedingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticThirdPrecedingIso_incoming_assoc, arithmeticThirdPreceding_chart]

omit m in
/-- Both preceding global edges have identity residual on the third layer. -/
@[reassoc] theorem arithmeticThirdAtlas_preceding_third (b : Bool) :
    leftBranchOpen (Quotient R π 3)
        (arithmeticThirdEarlierSmoothing hπ data H j hj u hu 3 b) ≫
      (arithmeticThirdEarlierIdentification hπ data H 3 j hj u hu a ha b).hom ≫
        arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 3)
          (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu 3 b) ≫
        (arithmeticThirdPrecedingIdentification hπ data H 3 j hj u hu (a + 1)
          (by omega) b).hom ≫
            arithmeticThirdAtlasChart hπ data H 3 j hj u hu (.retained ⟨a + 1, by omega⟩ b) := by
  have h := arithmeticThirdAtlas_residual_preceding hπ data H 3 j hj u hu a ha b
  rw [← arithmeticThirdPrecedingEquiv_spec, arithmeticThirdPrecedingEquiv_third,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
