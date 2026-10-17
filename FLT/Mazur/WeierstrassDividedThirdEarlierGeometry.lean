/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdTransitions
public import FLT.Mazur.WeierstrassDividedThirdAtlasIdentification
public import FLT.Mazur.WeierstrassDividedSecondPrecedingAdjacent

/-!
# The full earlier correction and the predecessor's incoming third transition

The earlier correction is installed only when its retained label exists.
The predecessor's other puncture keeps its exact new smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticThirdEarlierOrientedIso arithmeticThirdAtlasChart arithmeticSecondJointAtlasChart
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticSecondPrecedingSmoothing hπ data H m j hj u hu
local notation "t" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticThirdPrecedingIntegralField hπ data H j hj u hu
local notation "v" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticThirdEarlierOrientedIso hπ data H m j hj u hu

/-- The predecessor's opposite correction in its original incoming edge coordinate. -/
def arithmeticThirdPrecedingEdgeIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫
    punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (V b) false) ≪≫
      (edgeInversion Q).symm

local notation "K" => arithmeticThirdPrecedingEdgeIso hπ data H m j hj u hu

/-- The opposite predecessor puncture retains both its old and third smoothing. -/
@[reassoc] theorem arithmeticThirdPrecedingIso_incoming (b : Bool) :
    precedingBranch Q (s b) ≫ (arithmeticThirdPrecedingIso hπ data H m j hj u hu b).hom =
      (K b).hom ≫ precedingBranch Q (t b) := by
  have h := arithmeticThirdPrecedingIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticThirdPrecedingEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The earlier retained correction carries its full positive outgoing substitution. -/
@[reassoc] theorem arithmeticThirdEarlierOrientedIso_outgoing (b : Bool) :
    (leftBranchOpen Q τ ≫ (O b).hom) ≫ (C b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ (v b) true)).hom ≫
        leftBranchOpen Q (e b) := by
  rw [Category.assoc, arithmeticThirdEarlierOrientedIso_hom]
  simpa only [punctureOpen_true] using
    arithmeticThirdEarlierIso_puncture hπ data H m j hj u hu b true

/-- The full preceding residual in geometric composition order. -/
def arithmeticThirdPrecedingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (correctionPunctureFactor R π m τ (v b) true)).symm ≪≫
    arithmeticSecondPrecedingIncomingIso hπ data H m j hj u hu b ≪≫ K b

/-- The algebraic opposite substitution gives the exact incoming geometric correction. -/
theorem arithmeticThirdPrecedingEdgeEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticThirdPrecedingEdgeEquiv hπ data H j hj u hu m b) = K b := by
  simp only [arithmeticThirdPrecedingEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticThirdPrecedingEdgeIso]
  rfl

/-- The preceding algebraic cancellation belongs to the actual geometric residual. -/
theorem arithmeticThirdPrecedingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticThirdPrecedingEquiv hπ data H j hj u hu m b) =
      arithmeticThirdPrecedingResidual hπ data H m j hj u hu b := by
  rw [arithmeticThirdPrecedingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticSecondPrecedingIncomingEquiv_spec,
    arithmeticThirdPrecedingEdgeEquiv_spec]
  rfl

variable [IsBezout R] (a : ℕ) (ha : a + 2 = j)
local notation "N" => arithmeticSecondJointEarlierIdentification hπ data H m j hj u hu
local notation "A" => arithmeticThirdAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticThirdAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticThirdAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticSecondJointAtlasChart hπ data H m j hj u hu

/-- The earlier retained label has the full positive correction's exact smoothing. -/
def arithmeticThirdEarlierIdentification (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅ A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticThirdAtlasObject,
    show ¬a + 1 = j by omega, ha, ↓reduceIte])

local notation "D" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The installed earlier correction starts at the actual unchanged second-atlas label. -/
theorem arithmeticThirdAtlasCorrection_earlier (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) =
      (N ⟨a, by omega⟩ (show a + 1 < j by omega) b).symm ≪≫ C b ≪≫ D b := by
  simp only [arithmeticThirdAtlasCorrection, show ¬a + 1 = j by omega, ha, ↓reduceDIte]
  rfl

/-- The earlier third chart recovers its actual old global inclusion. -/
@[reassoc] theorem arithmeticThirdEarlier_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (N ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticThirdAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticThirdAtlasCorrection_earlier hπ data H m j hj u hu a ha b] at h
  have hh := congrArg
    (fun f ↦ (N ⟨a, by omega⟩ (show a + 1 < j by omega) b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
