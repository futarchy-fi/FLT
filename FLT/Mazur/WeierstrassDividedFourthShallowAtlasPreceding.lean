/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthShallowCancellation
public import FLT.Mazur.WeierstrassDividedFourthOuterTransitions
public import FLT.Mazur.WeierstrassDividedFourthShallowPreceding
public import FLT.Mazur.WeierstrassDividedThirdAtlasPreceding

/-!
# The actual preceding edge of the fourth depth-two atlas

The same whole earlier factor used on the initial edge also cancels
the preceding edge, with both exact changed smoothings retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthPrecedingIso arithmeticFourthShallowNeighborIso arithmeticFourthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (ha : 2 = j)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "ι" => arithmeticFourthShallowAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "N" => arithmeticFourthShallowPrecedingIdentification
  hπ data H m j hj u hu 1 (by omega) (by omega)
local notation "M" => arithmeticFourthShallowNeighborIdentification hπ data H m j hj u hu ha
local notation "N₂" => arithmeticThirdPrecedingIdentification
  hπ data H m j hj u hu 1 (by omega)
local notation "M₂" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu 0 ha
local notation "s" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "s₂" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthShallowNeighborIntegralField hπ data H j hj u hu

/-- The installed preceding edge has precisely the full fourth Laurent residual. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_residual_preceding (b : Bool) :
    leftBranchOpen Q (s b) ≫ (M b).hom ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticFourthShallowNeighborIncomingEquiv hπ data H j hj u hu m b)).hom ≫
        precedingBranch Q (t b) ≫ (N b).hom ≫ ι (.retained ⟨1, by omega⟩ b) := by
  have hP := arithmeticFourthShallowNeighborIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (e₃ b) (V b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (e₃ b) ≫ (M₂ b).hom ≫
        κ (.retained ⟨0, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)),
        ← hP, Category.assoc,
        arithmeticFourthShallowNeighbor_chart]
    _ = (arithmeticThirdPrecedingResidual hπ data H m j hj u hu b).hom ≫
        precedingBranch Q (s₂ b) ≫ (N₂ b).hom ≫
          κ (.retained ⟨1, by omega⟩ b) :=
      by simpa only [arithmeticThirdInitialAtlasChart_retained] using
        arithmeticThirdAtlas_residual_preceding hπ data H m j hj u hu 0 ha b
    _ = _ := by
      simp only [arithmeticFourthShallowNeighborIncomingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticThirdPrecedingEquiv_spec,
        arithmeticFourthPrecedingEdgeEquiv_spec, Iso.trans_hom, Iso.symm_hom,
        Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFourthPrecedingIso_incoming_assoc, arithmeticFourthShallowPreceding_chart]

omit m in
/-- Both preceding global edges have identity residual on the fourth layer. -/
@[reassoc] theorem arithmeticFourthShallowAtlas_preceding_fourth (b : Bool) :
    leftBranchOpen (Quotient R π 4)
        (arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu 4 b) ≫
      (arithmeticFourthShallowNeighborIdentification hπ data H 4 j hj u hu ha b).hom ≫
        arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu (.retained ⟨0, by omega⟩ b) =
      precedingBranch (Quotient R π 4)
          (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu 4 b) ≫
        (arithmeticFourthShallowPrecedingIdentification hπ data H 4 j hj u hu 1
          (by omega) (by omega) b).hom ≫
            arithmeticFourthShallowAtlasChart hπ data H 4 j hj u hu
              (.retained ⟨1, by omega⟩ b) := by
  have h := arithmeticFourthShallowAtlas_residual_preceding hπ data H 4 j hj u hu ha b
  rw [arithmeticFourthShallowNeighborIncomingEquiv_fourth,
    punctureSpecIso_refl, Iso.refl_hom] at h
  simpa only [branchTorus, Category.id_comp] using h

end FLT.Mazur.WeierstrassDividedDepth
