/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedSecondJointGeometry

/-!
# Geometric transitions for the simultaneous second corrections

The full algebra formulas are identified with their geometric compositions.
Incoming and closing substitutions use the same shared retained node.
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
  (arithmeticSecondJointRetainedIntegralField hπ data H j hj u hu b)
local notation "S" => arithmeticSecondResidualLiftTerminalPuncture hπ data H m j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticSecondJointOrientedIso hπ data H m j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H m

/-- Express either retained puncture substitution in the original inverse edge coordinate. -/
def arithmeticSecondJointEdgeIso (b a : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso (A b a) ≪≫ (edgeInversion Q).symm

local notation "K" => arithmeticSecondJointEdgeIso hπ data H m j hj u hu

/-- The closing overlap carries the full conjugated outgoing retained substitution. -/
@[reassoc] theorem arithmeticSecondJointOrientedIso_closing (b : Bool) :
    (L ≫ (O b).hom) ≫ (C b).hom = (K b true).hom ≫ L ≫ (O b).hom := by
  have h := arithmeticSecondJointRetainedIso_puncture hπ data H m j hj u hu b true
  have ho := arithmeticSecondJointOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_true] at h
  simp only [arithmeticSecondJointEdgeIso, Iso.trans_hom, Iso.symm_hom,
    arithmeticClosingRetainedBoundary, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (leftBranchOpen Q τ), h, Category.assoc]

/-- The incoming edge carries its own full opposite-puncture substitution. -/
@[reassoc] theorem arithmeticSecondJointOrientedIso_incoming (b : Bool) :
    (precedingBranch Q τ ≫ (O b).hom) ≫ (C b).hom =
      (K b false).hom ≫ precedingBranch Q τ ≫ (O b).hom := by
  have h := arithmeticSecondJointRetainedIso_puncture hπ data H m j hj u hu b false
  have ho := arithmeticSecondJointOrientedIso_hom hπ data H m j hj u hu b
  rw [punctureOpen_false] at h
  simp only [arithmeticSecondJointEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [ho, ← Category.assoc (rightBranchOpen Q τ), h, Category.assoc]

/-- The actual residual after both lifted corrections, in geometric composition order. -/
def arithmeticSecondJointClosingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (K b true).symm ≪≫ arithmeticResidualLiftClosingResidual hπ data H m j hj u hu b ≪≫
    punctureSpecIso (S b).symm


/-- The incoming geometric residual includes the predecessor's outgoing inverse. -/
def arithmeticSecondJointIncomingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (arithmeticSecondPrecedingPuncture hπ data H m j hj u hu b)).symm ≪≫
    arithmeticResidualLiftEdgeIso hπ data H m j hj u hu b false ≪≫ K b false

/-- The whole joint edge formula gives exactly its oriented geometric edge. -/
theorem arithmeticSecondJointEdgeEquiv_spec (b a : Bool) :
    punctureSpecIso (arithmeticSecondJointEdgeEquiv hπ data H m j hj u hu b a) = K b a := by
  simp only [arithmeticSecondJointEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticSecondJointEdgeIso]
  rfl

/-- The full incoming algebra formula is the actual geometric transition composition. -/
theorem arithmeticSecondJointIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticSecondJointIncomingEquiv hπ data H m j hj u hu b) =
      arithmeticSecondJointIncomingResidual hπ data H m j hj u hu b := by
  rw [arithmeticSecondJointIncomingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticResidualLiftEdgeEquiv_spec,
    arithmeticSecondJointEdgeEquiv_spec]
  rfl

/-- The closing algebra formula has the contravariant order of the actual chart changes. -/
theorem arithmeticSecondJointClosingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticSecondJointClosingEquiv hπ data H m j hj u hu b) =
      arithmeticSecondJointClosingResidual hπ data H m j hj u hu b := by
  rw [arithmeticSecondJointClosingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticSecondJointEdgeEquiv_spec,
    arithmeticResidualLiftClosingEquiv_spec]
  rfl

/-- The preceding outgoing puncture square uses its changed smoothing. -/
@[reassoc] theorem arithmeticSecondPrecedingOrientedIso_outgoing (b : Bool) :
    (leftBranchOpen Q τ ≫ (O b).hom) ≫
        (arithmeticSecondPrecedingOrientedIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (arithmeticSecondPrecedingPuncture hπ data H m j hj u hu b)).hom ≫
        leftBranchOpen Q (arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu b) := by
  rw [Category.assoc, arithmeticSecondPrecedingOrientedIso_hom]
  simpa only [punctureOpen_true, arithmeticSecondPrecedingPuncture] using
    arithmeticSecondPrecedingIso_puncture hπ data H m j hj u hu b true

end FLT.Mazur.WeierstrassDividedDepth
