/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowAtlasIdentification
public import FLT.Mazur.WeierstrassDividedFifthShallowTransitions
public import FLT.Mazur.WeierstrassDividedFourthShallowAtlasPreceding
public import FLT.Mazur.WeierstrassDividedFifthShallowIncomingCancellation

/-!
# The actual preceding overlap of the fifth depth-two atlas

The earlier neighbor shares one full factor with the initial edge. The
predecessor shares its full factor with the incoming edge to the last node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFifthShallowPrecedingIso arithmeticFifthShallowAtlasChart
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 3 ≤ n)
  (u : Rˣ) (hu : (data ⟨3, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "ι" => arithmeticFifthShallowAtlasChart hπ data H m hj u hu
local notation "κ" => arithmeticFourthShallowAtlasChart hπ data H m 2 hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "L" => arithmeticClosingRetainedBoundary data H m
local notation "s" => arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu m
local notation "s₄" => arithmeticFourthShallowNeighborSmoothing hπ data H 2 hj u hu m
local notation "t" => arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu m
local notation "t₄" => arithmeticFourthPrecedingSmoothing hπ data H 2 hj u hu m
local notation "P" => arithmeticFifthShallowNeighborIntegralField hπ data H 2 hj u hu
local notation "M" => arithmeticFourthShallowNeighborIdentification hπ data H m 2 hj u hu rfl
local notation "N" => arithmeticFourthShallowPrecedingIdentification
  hπ data H m 2 hj u hu 1 rfl (by omega)

/-- The actual preceding edge has the full fifth residual from both shared node factors. -/
@[reassoc] theorem arithmeticFifthShallowAtlas_residual_preceding (b : Bool) :
    leftBranchOpen Q (s b) ≫ ι (.retained ⟨0, by omega⟩ b) =
      (punctureSpecIso (arithmeticFifthShallowPrecedingEquiv hπ data H 2 hj u hu m b)).hom ≫
        precedingBranch Q (t b) ≫ ι (.retained ⟨1, by omega⟩ b) := by
  have hP := arithmeticFifthShallowNeighborIso_puncture hπ data H m 2 hj u hu b true
  simp only [punctureOpen_true] at hP
  apply (cancel_epi
    (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₄ b) (P b) true)).hom).mp
  calc
    _ = leftBranchOpen Q (s₄ b) ≫ (M b).hom ≫ κ (.retained ⟨0, by omega⟩ b) := by
      rw [← Category.assoc _ (leftBranchOpen Q (s b)), ← hP, Category.assoc,
        arithmeticFifthShallowNeighbor_chart]
    _ = (punctureSpecIso
          (arithmeticFourthShallowNeighborIncomingEquiv hπ data H 2 hj u hu m b)).hom ≫
        precedingBranch Q (t₄ b) ≫ (N b).hom ≫ κ (.retained ⟨1, by omega⟩ b) :=
      arithmeticFourthShallowAtlas_residual_preceding hπ data H m 2 hj u hu rfl b
    _ = _ := by
      simp only [arithmeticFifthShallowPrecedingEquiv, punctureSpecIso_trans,
        punctureSpecIso_symm, arithmeticFifthShallowPrecedingEdgeEquiv_spec,
        Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
      rw [← arithmeticFifthShallowPrecedingIso_incoming_assoc,
        arithmeticFifthShallowPreceding_chart]

omit m in
/-- Both actual preceding residuals vanish on the fifth layer. -/
@[reassoc] theorem arithmeticFifthShallowAtlas_preceding_fifth (b : Bool) :
    leftBranchOpen (Quotient R π 5)
        (arithmeticFifthShallowNeighborSmoothing hπ data H 2 hj u hu 5 b) ≫
      arithmeticFifthShallowAtlasChart hπ data H 5 hj u hu (.retained ⟨0, by omega⟩ b) =
      precedingBranch (Quotient R π 5)
          (arithmeticFifthShallowPrecedingSmoothing hπ data H 2 hj u hu 5 b) ≫
        arithmeticFifthShallowAtlasChart hπ data H 5 hj u hu (.retained ⟨1, by omega⟩ b) := by
  rw [arithmeticFifthShallowAtlas_residual_preceding, arithmeticFifthShallowPrecedingEquiv_fifth,
    punctureSpecIso_refl, Iso.refl_hom]
  exact Category.id_comp _

end FLT.Mazur.WeierstrassDividedDepth
