/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialLast
public import FLT.Mazur.WeierstrassDividedFourthInitialCancellation
public import FLT.Mazur.WeierstrassDividedFourthTransitions
public import FLT.Mazur.WeierstrassDividedThirdAtlasIncoming

/-!
# The shared incoming edges of the depth-one fourth atlas

The same last factor serves the closing and incoming edges. Its predecessor
keeps all earlier and fourth smoothing drifts in the global diagram.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthInitialNeighborIso arithmeticFourthInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha : 1 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticFourthInitialAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "P" => arithmeticFourthInitialNeighborIso hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticFourthInitialLastIdentification hπ data H m j hj u hu
local notation "M" => arithmeticFourthInitialNeighborIdentification hπ data H m j hj u hu ha
local notation "N₂" => arithmeticThirdLastIdentification hπ data H m j hj u hu
local notation "M₂" => arithmeticThirdPrecedingIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m
local notation "s₂" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthInitialNeighborIntegralField hπ data H j hj u hu

/-- The installed incoming edge has exactly the full fourth algebraic residual. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso
        (arithmeticFourthInitialNeighborIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫
          ι (.retained ⟨j, by omega⟩ b) := by
  have hP := arithmeticFourthInitialNeighborIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₂ b) (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₂ b) ≫ (M₂ b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← hP, Category.assoc,
        arithmeticFourthInitialNeighbor_chart]
    _ = (arithmeticThirdIncomingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N₂ b).hom ≫
          κ (.retained ⟨j, by omega⟩ b) :=
      by simpa only [arithmeticThirdInitialAtlasChart_retained] using
        arithmeticThirdAtlas_residual_incoming hπ data H m j hj u hu 0 ha b
    _ = _ := by
      simp only [arithmeticFourthInitialNeighborIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticThirdIncomingEquiv_spec,
        arithmeticFourthLastEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFourthLastOrientedIso_incoming_assoc,
        arithmeticFourthInitialLast_chart]

omit m in
/-- Both actual incoming edges have identity residual on the fourth layer. -/
@[reassoc] theorem arithmeticFourthInitialAtlas_incoming_fourth (b : Bool) :
    leftBranchOpen (Quotient R π 4)
        (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu 4 b) ≫
      (arithmeticFourthInitialNeighborIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu (.retained ⟨0, by omega⟩ b) =
      precedingBranch (Quotient R π 4)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 4) ≫
        (twistedRetainedOrientation data H 4 b).hom ≫
          (arithmeticFourthInitialLastIdentification hπ data H 4 j hj u hu b).hom ≫
            arithmeticFourthInitialAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨j, by omega⟩ b) := by
  have h := arithmeticFourthInitialAtlas_residual_incoming hπ data H 4 j hj u hu ha b
  rw [arithmeticFourthInitialNeighborIncomingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
