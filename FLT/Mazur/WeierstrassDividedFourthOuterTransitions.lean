/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthOuterCancellation
public import FLT.Mazur.WeierstrassDividedFourthOuterGeometry
public import FLT.Mazur.WeierstrassDividedFourthEarlierGeometry

/-!
# Geometric residuals for the simultaneous outer fourth correction

The two branches of the same earlier node supply the incoming and preceding
substitutions. Their geometric order matches the full algebraic residuals.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
  (m : ℕ)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m

local notation "P" => arithmeticFourthOuterIntegralField hπ data H j hj u hu
local notation "F" => arithmeticFourthFartherIntegralField hπ data H j hj u hu

/-- The earlier incoming substitution in the actual reciprocal retained coordinate. -/
def arithmeticFourthOuterEdgeIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫ punctureSpecIso
    (twoBranchCorrectionPunctureFactor R π m (s₃ b) (P b) false) ≪≫ (edgeInversion Q).symm

/-- The full incoming puncture square uses the earlier node's exact new smoothing. -/
@[reassoc] theorem arithmeticFourthOuterIso_incoming (b : Bool) :
    precedingBranch Q (s₃ b) ≫ (arithmeticFourthOuterIso hπ data H j hj u hu m b).hom =
      (arithmeticFourthOuterEdgeIso hπ data H j hj u hu m b).hom ≫
        precedingBranch Q (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) := by
  have h := arithmeticFourthOuterIso_puncture hπ data H j hj u hu m b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFourthOuterEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The other branch of the same whole-node factor supplies the outgoing square. -/
@[reassoc] theorem arithmeticFourthOuterIso_outgoing (b : Bool) :
    leftBranchOpen Q (s₃ b) ≫ (arithmeticFourthOuterIso hπ data H j hj u hu m b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₃ b) (P b) true)).hom ≫
        leftBranchOpen Q (arithmeticFourthOuterSmoothing hπ data H j hj u hu m b) := by
  simpa only [punctureOpen_true] using
    arithmeticFourthOuterIso_puncture hπ data H j hj u hu m b true

/-- The farther full positive factor supplies the other end of the incoming edge. -/
@[reassoc] theorem arithmeticFourthFartherIso_outgoing (b : Bool) :
    leftBranchOpen Q τ ≫ (arithmeticFourthFartherIso hπ data H j hj u hu m b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ (F b) true)).hom ≫
        leftBranchOpen Q (arithmeticFourthFartherSmoothing hπ data H j hj u hu m b) := by
  simpa only [punctureOpen_true] using
    arithmeticFourthFartherIso_puncture hπ data H j hj u hu m b true

/-- The further incoming residual in geometric composition order. -/
def arithmeticFourthOuterIncomingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (correctionPunctureFactor R π m τ (F b) true)).symm ≪≫
    arithmeticThirdEarlierIncomingIso hπ data H m j hj u hu b ≪≫
      arithmeticFourthOuterEdgeIso hπ data H j hj u hu m b

/-- The preceding residual uses the same full earlier factor. -/
def arithmeticFourthOuterPrecedingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s₃ b) (P b) true)).symm ≪≫
    arithmeticThirdPrecedingResidual hπ data H m j hj u hu b ≪≫
      arithmeticFourthPrecedingEdgeIso hπ data H m j hj u hu b

/-- The reciprocal algebraic substitution is the actual incoming geometric factor. -/
theorem arithmeticFourthOuterEdgeEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthOuterEdgeEquiv hπ data H j hj u hu m b) =
      arithmeticFourthOuterEdgeIso hπ data H j hj u hu m b := by
  simp only [arithmeticFourthOuterEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFourthOuterEdgeIso]
  rfl

/-- The complete incoming algebraic residual has the exact geometric composition order. -/
theorem arithmeticFourthOuterIncomingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthOuterIncomingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthOuterIncomingResidual hπ data H j hj u hu m b := by
  rw [arithmeticFourthOuterIncomingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticThirdEarlierIncomingEquiv_spec,
    arithmeticFourthOuterEdgeEquiv_spec]
  rfl

/-- The complete preceding algebraic residual is realized by the same whole earlier factor. -/
theorem arithmeticFourthOuterPrecedingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthOuterPrecedingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthOuterPrecedingResidual hπ data H j hj u hu m b := by
  rw [arithmeticFourthOuterPrecedingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticThirdPrecedingEquiv_spec,
    arithmeticFourthPrecedingEdgeEquiv_spec]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
