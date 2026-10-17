/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasClosing
public import FLT.Mazur.WeierstrassDividedFourthShallowPreceding
public import FLT.Mazur.WeierstrassDividedFourthIncomingCancellation
public import FLT.Mazur.WeierstrassDividedThirdAtlasIncoming

/-!
# The shared incoming edges of the depth-two fourth atlas

The same last factor serves the closing and incoming edges. Its predecessor
keeps all earlier and fourth smoothing drifts in the global diagram.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthPrecedingIso arithmeticFourthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "P" => arithmeticFourthPrecedingIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticFourthShallowLastIdentification hπ data H m j hj u hu
local notation "N₂" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "s" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "s₂" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu

/-- The last node keeps its full comparison with the same third source. -/
@[reassoc] theorem arithmeticFourthShallowLast_chart (b : Bool) :
    (arithmeticFourthLastOrientedIso hπ data H m j hj u hu b).hom ≫
      (N b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
        (N₂ b).hom ≫ κ (.retained ⟨j, by omega⟩ b) := by
  rw [arithmeticFourthShallowLast_chart_eq, arithmeticFourthOuterLast_chart_eq,
    arithmeticFourthInitialLast_chart]

variable (a : ℕ) (ha : a + 1 = j) (hj₂ : 2 ≤ j)
local notation "M" => arithmeticFourthShallowPrecedingIdentification hπ data H m j hj u hu a ha hj₂
local notation "M₂" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu a ha

/-- The installed incoming edge has exactly the full fourth algebraic residual. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (arithmeticFourthIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫
          ι (.retained ⟨j, by omega⟩ b) := by
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₂ b) ≫ (M₂ b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← arithmeticFourthPrecedingIso_outgoing, Category.assoc,
        arithmeticFourthShallowPreceding_chart]
    _ = (arithmeticThirdIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N₂ b).hom ≫
          κ (.retained ⟨j, by omega⟩ b) :=
      by simpa only [arithmeticThirdInitialAtlasChart_retained] using
        arithmeticThirdAtlas_residual_incoming hπ data H m j hj u hu a ha b
    _ = _ := by
      simp only [arithmeticFourthIncomingResidual, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFourthLastOrientedIso_incoming_assoc,
        arithmeticFourthShallowLast_chart]

omit m in
/-- Both actual incoming edges have identity residual on the fourth layer. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_incoming_fourth (b : Bool) :
    leftBranchOpen (Quotient R π 4)
        (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu 4 b) ≫
      (arithmeticFourthShallowPrecedingIdentification hπ data H 4 j hj u hu a ha hj₂ b).hom ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu (.retained ⟨a, by omega⟩ b) =
      precedingBranch (Quotient R π 4)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4) ≫
        (twistedRetainedOrientation data H 4 b).hom ≫
          (arithmeticFourthShallowLastIdentification hπ data H 4 j hj u hu b).hom ≫
            arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticFourthShallowAtlas_residual_incoming hπ data H 4 j hj u hu a ha hj₂ b
  rw [← arithmeticFourthIncomingEquiv_spec, arithmeticFourthIncomingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
