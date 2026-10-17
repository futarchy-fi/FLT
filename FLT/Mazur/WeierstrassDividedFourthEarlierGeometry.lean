/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthTransitions
public import FLT.Mazur.WeierstrassDividedFourthAtlasIdentification
public import FLT.Mazur.WeierstrassDividedThirdEarlierGeometry

/-!
# The full earlier correction and the predecessor's incoming fourth transition

The earlier correction is installed only when its retained label exists.
The predecessor's other puncture keeps its exact new smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticFourthEarlierIso arithmeticFourthAtlasChart arithmeticThirdInitialAtlasChart
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "t" => arithmeticFourthPrecedingSmoothing hπ data H j hj u hu m
local notation "e" => arithmeticFourthEarlierSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthPrecedingIntegralField hπ data H j hj u hu
local notation "e₃" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "v" => arithmeticFourthEarlierIntegralField hπ data H j hj u hu
local notation "O" => twistedRetainedOrientation data H m
local notation "C" => arithmeticFourthEarlierIso hπ data H m j hj u hu

/-- The predecessor's opposite correction in its original incoming edge coordinate. -/
def arithmeticFourthPrecedingEdgeIso (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  edgeInversion Q ≪≫
    punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (V b) false) ≪≫
      (edgeInversion Q).symm

local notation "K" => arithmeticFourthPrecedingEdgeIso hπ data H m j hj u hu

/-- The opposite predecessor puncture retains both its old and fourth smoothing. -/
@[reassoc] theorem arithmeticFourthPrecedingIso_incoming (b : Bool) :
    precedingBranch Q (s b) ≫ (arithmeticFourthPrecedingIso hπ data H m j hj u hu b).hom =
      (K b).hom ≫ precedingBranch Q (t b) := by
  have h := arithmeticFourthPrecedingIso_puncture hπ data H m j hj u hu b false
  simp only [punctureOpen_false] at h
  simp only [arithmeticFourthPrecedingEdgeIso, Iso.trans_hom, Iso.symm_hom,
    precedingBranch, Category.assoc, Iso.inv_hom_id_assoc]
  rw [h]

/-- The earlier retained correction carries its full positive outgoing substitution. -/
@[reassoc] theorem arithmeticFourthEarlierIso_outgoing (b : Bool) :
    leftBranchOpen Q (e₃ b) ≫ (C b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e₃ b) (v b) true)).hom ≫
        leftBranchOpen Q (e b) := by
  simpa only [punctureOpen_true] using
    arithmeticFourthEarlierIso_puncture hπ data H m j hj u hu b true

/-- The full preceding residual in geometric composition order. -/
def arithmeticFourthPrecedingResidual (b : Bool) : branchTorus Q ≅ branchTorus Q :=
  (punctureSpecIso (correctionPunctureFactor R π m (e₃ b) (v b) true)).symm ≪≫
    arithmeticThirdPrecedingResidual hπ data H m j hj u hu b ≪≫ K b

/-- The algebraic opposite substitution gives the exact incoming geometric correction. -/
theorem arithmeticFourthPrecedingEdgeEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthPrecedingEdgeEquiv hπ data H j hj u hu m b) = K b := by
  simp only [arithmeticFourthPrecedingEdgeEquiv, punctureSpecIso_trans,
    punctureSpecIso_invert, arithmeticFourthPrecedingEdgeIso]
  rfl

/-- The preceding algebraic cancellation belongs to the actual geometric residual. -/
theorem arithmeticFourthPrecedingEquiv_spec (b : Bool) :
    punctureSpecIso (arithmeticFourthPrecedingEquiv hπ data H j hj u hu m b) =
      arithmeticFourthPrecedingResidual hπ data H m j hj u hu b := by
  rw [arithmeticFourthPrecedingEquiv, punctureSpecIso_trans, punctureSpecIso_trans,
    punctureSpecIso_symm, arithmeticThirdPrecedingEquiv_spec,
    arithmeticFourthPrecedingEdgeEquiv_spec]
  rfl

variable [IsBezout R] (a : ℕ) (ha : a + 2 = j)
local notation "N" => arithmeticThirdEarlierIdentification hπ data H m j hj u hu a ha
local notation "A" => arithmeticFourthAtlasObject hπ data H m j hj u hu
local notation "E" => arithmeticFourthAtlasCorrection hπ data H m j hj u hu
local notation "ι" => arithmeticFourthAtlasChart hπ data H m j hj u hu
local notation "κ" => arithmeticThirdInitialAtlasChart hπ data H m j hj u hu

/-- The earlier retained label has the full positive correction's exact smoothing. -/
def arithmeticFourthEarlierIdentification (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅ A (.retained ⟨a, by omega⟩ b) :=
  eqToIso (by simp only [arithmeticFourthAtlasObject,
    show ¬a + 1 = j by omega, ha, ↓reduceIte])

local notation "D" => arithmeticFourthEarlierIdentification hπ data H m j hj u hu a ha

omit [IsBezout R] in
/-- The installed earlier correction starts at the actual third-atlas label. -/
theorem arithmeticFourthAtlasCorrection_earlier (b : Bool) :
    E (.retained ⟨a, by omega⟩ b) =
      (N b).symm ≪≫ C b ≪≫ D b := by
  simp only [arithmeticFourthAtlasCorrection, show ¬a + 1 = j by omega, ha, ↓reduceDIte]
  rfl

/-- The earlier fourth chart recovers its actual old global inclusion. -/
@[reassoc] theorem arithmeticFourthEarlier_chart (b : Bool) :
    (C b).hom ≫ (D b).hom ≫ ι (.retained ⟨a, by omega⟩ b) =
      (N b).hom ≫ κ (.retained ⟨a, by omega⟩ b) := by
  have h := arithmeticFourthAtlasCorrection_chart hπ data H m j hj u hu
    (.retained ⟨a, by omega⟩ b)
  rw [arithmeticFourthAtlasCorrection_earlier hπ data H m j hj u hu a ha b] at h
  have hh := congrArg
    (fun f ↦ (N b).hom ≫ f) h
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc] using hh

end FLT.Mazur.WeierstrassDividedDepth
