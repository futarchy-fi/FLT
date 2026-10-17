/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthTerminalGeometry
public import FLT.Mazur.WeierstrassDividedFourthResidualAlgebra
public import FLT.Mazur.WeierstrassDividedThirdTransitions

/-!
# Geometric transitions for the full fourth corrections

The full algebra formulas are identified with their geometric compositions.
Incoming and closing substitutions use the same shared retained node and
its actual prior smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "A" => fun b ↦ twoBranchCorrectionPunctureFactor R π m τ
  (arithmeticFourthLastIntegralField hπ data H j hj u hu b)
local notation "S" => fun b ↦ twoBranchCorrectionRebasedPunctureFactor R π m
  (arithmeticThirdTerminalSmoothing hπ data H j hj u hu m)
    (arithmeticFourthTerminalIntegralField hπ data H j hj u hu) b
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFourthLastOrientedIso hπ data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m

/-- Express either retained puncture substitution in the original inverse edge coordinate. -/
def arithmeticFourthLastEdgeIso (b a : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (A b a) ≪≫ (edgeInversion Q).symm

local notation "K" => arithmeticFourthLastEdgeIso hπ data H m j hj u hu

/-- The closing overlap carries the full conjugated outgoing retained substitution. -/
@[reassoc] theorem arithmeticFourthLastOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b true).hom ≫ L ≫ (O b).hom := by
  have h := arithmeticFourthLastIso_puncture hπ data H m j hj u hu b true
  have ho := arithmeticFourthLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_true] at h
  simp only [arithmeticFourthLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    arithmeticClosingRetainedBoundary, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (leftBranchOpen Q τ), h, Category.assoc]

/-- The incoming edge carries its own full opposite-puncture substitution. -/
@[reassoc] theorem arithmeticFourthLastOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      (K b false).hom ≫ precedingBranch Q τ ≫ (O b).hom := by
  have h := arithmeticFourthLastIso_puncture hπ data H m j hj u hu b false
  have ho := arithmeticFourthLastOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_false] at h
  simp only [arithmeticFourthLastEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (rightBranchOpen Q τ), h, Category.assoc]

/-- The actual residual after both lifted corrections, in geometric composition order. -/
def arithmeticFourthClosingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (K b true).symm ≪≫ arithmeticThirdClosingResidual hπ data H m j hj u hu b ≪≫
    punctureSpecIso (S b).symm


/-- The incoming geometric residual includes the predecessor's outgoing inverse. -/
def arithmeticFourthIncomingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m
      (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b)
      (arithmeticFourthPrecedingIntegralField hπ data H j hj u hu b) true)).symm ≪≫
    arithmeticThirdIncomingResidual hπ data H m j hj u hu b ≪≫ K b false

/-- The whole joint edge formula gives exactly its oriented geometric edge. -/
theorem arithmeticFourthLastEdgeEquiv_spec (b a : Bool) :
    punctureSpecIso (arithmeticFourthLastEdgeEquiv hπ data H j hj u hu m b a) = K b a := by
  simp only [arithmeticFourthLastEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFourthLastEdgeIso]
  rfl

/-- The full incoming algebra formula is the actual geometric transition composition. -/
theorem arithmeticFourthIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthIncomingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthIncomingResidual hπ data H m j hj u hu b := by
  rw [arithmeticFourthIncomingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticThirdIncomingEquiv_spec,
    arithmeticFourthLastEdgeEquiv_spec]
  rfl

/-- The closing algebra formula has the contravariant order of the actual chart changes. -/
theorem arithmeticFourthClosingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthClosingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthClosingResidual hπ data H m j hj u hu b := by
  rw [arithmeticFourthClosingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticFourthLastEdgeEquiv_spec,
    arithmeticThirdClosingEquiv_spec]
  rfl

/-- The predecessor's outgoing puncture uses its actual old and new smoothing. -/
@[reassoc] theorem arithmeticFourthPrecedingIso_outgoing (b : Bool) :
    leftBranchOpen Q (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b) ≫
        (arithmeticFourthPrecedingIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m
        (arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m b)
        (arithmeticFourthPrecedingIntegralField hπ data H j hj u hu b) true)).hom ≫
          leftBranchOpen Q (arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m b) := by
  simpa only [punctureOpen_true] using
    arithmeticFourthPrecedingIso_puncture hπ data H m j hj u hu b true

end FLT.Mazur.WeierstrassDividedDepth
