/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthInitialAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthInitialTransitions
public import FLT.Mazur.WeierstrassDividedFourthInitialAtlasIncoming
public import FLT.Mazur.WeierstrassDividedFifthInitialIncomingCancellation

/-!
# The actual incoming overlap of the fifth depth-one atlas

The last factor is shared with the closing edge. The full predecessor factor
retains the exact fourth and fifth smoothing in the global comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthInitialNeighborIso arithmeticFifthInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 2 ≤ n)
  (u : Rˣ) (hu : (data ⟨2, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthInitialAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthInitialAtlasChart hπ data H m 1 hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu m
local notation "s₄" => arithmeticFourthInitialNeighborSmoothing hπ data H 1 hj u hu m
local notation "P" => arithmeticFifthInitialNeighborIntegralField hπ data H 1 hj u hu
local notation "M" => arithmeticFourthInitialNeighborIdentification
  hπ data H m 1 hj u hu rfl
local notation "N" => arithmeticFourthInitialLastIdentification hπ data H m 1 hj u hu

/-- The installed incoming overlap is precisely the complete fifth residual. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_residual_incoming (b : Bool) :
    leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthInitialIncomingEquiv hπ data H 1 hj u hu m b)).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ ι (.retained ⟨1, by omega⟩ b) := by
  have hP := arithmeticFifthInitialNeighborIso_puncture hπ data H m 1 hj u hu b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₄ b) (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthInitialNeighbor_chart]
    _ = (punctureSpecIso
        (arithmeticFourthInitialNeighborIncomingEquiv hπ data H 1 hj u hu m b)).hom ≫
        precedingBranch Q τ ≫ (O b).hom ≫ (N b).hom ≫ κ (.retained ⟨1, by omega⟩ b) :=
      arithmeticFourthInitialAtlas_residual_incoming hπ data H m 1 hj u hu rfl b
    _ = _ := by
      simp only [arithmeticFifthInitialIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticFifthInitialLastEdgeEquiv_spec,
        Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFifthInitialLastOrientedIso_incoming_assoc,
        arithmeticFifthInitialLast_chart]

omit m in
/-- Both actual incoming residuals vanish on the fifth layer. -/
@[reassoc] theorem arithmeticFifthInitialAtlas_incoming_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthInitialNeighborSmoothing hπ data H 1 hj u hu 5 b) ≫
      arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu (.retained ⟨0, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 5) ≫
        (twistedRetainedOrientation data H 5 b).hom ≫
          arithmeticFifthInitialAtlasChart hπ data H 5 hj u hu (.retained ⟨1, by omega⟩ b) := by
  rw [arithmeticFifthInitialAtlas_residual_incoming, arithmeticFifthInitialIncomingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
