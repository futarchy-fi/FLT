/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroSecondNodes
public import FLT.Mazur.WeierstrassDividedZeroFirstGeometry

/-!
# Second geometry for the initial open and the shared last node

The full initial open is pulled through its second factor from its actual
first smoothing. The last full factor starts on that last node's first smoothing.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "e" => arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticZeroSecondInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticZeroSecondLastIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its exact first smoothing to its second. -/
def arithmeticZeroSecondInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroSecondInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticZeroSecondLastIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroSecondLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticZeroSecondInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticZeroSecondInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroSecondInitialFactor_puncture hπ data H j hj u hu m b a

/-- Both last punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticZeroSecondLastIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticZeroSecondLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroSecondLastFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticZeroSecondInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticZeroFirstInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the actual first initial open through the full second node comparison. -/
def arithmeticZeroSecondInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The first initial open is isomorphic to the constructed second initial open. -/
def arithmeticZeroSecondInitialIso (b : Bool) :
    arithmeticZeroFirstInitialObject hπ data H m j hj u hu b ≅
      arithmeticZeroSecondInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticZeroSecondInitialIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticZeroSecondInitialNodeChart (b : Bool) :
    arithmeticZeroSecondInitialObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticZeroSecondInitialNodeChart hπ data H m j hj u hu

instance arithmeticZeroSecondInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroSecondInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual first and second node maps. -/
@[reassoc] theorem arithmeticZeroSecondInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the actual first puncture with the second initial substitution. -/
def arithmeticZeroSecondInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroSecondInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ arithmeticZeroFirstInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticZeroSecondInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroSecondInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticZeroSecondInitialPuncture, Category.assoc,
    arithmeticZeroSecondInitialIso_nodeChart]
  rw [arithmeticZeroFirstInitialPuncture_nodeChart_assoc]
  have h := arithmeticZeroSecondInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticZeroSecondTerminalIso :
    PolygonSmoothing.chart Q (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) ≅
      PolygonSmoothing.chart Q (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticZeroSecondTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures are induced by this one full common terminal comparison. -/
@[reassoc] theorem arithmeticZeroSecondTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m) b ≫
        (arithmeticZeroSecondTerminalIso hπ data H m j hj u hu).hom =
      (punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
        (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m)
        (arithmeticZeroSecondTerminalIntegralField hπ data H j hj u hu) b).symm).hom ≫
          punctureOpen (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) b := by
  unfold arithmeticZeroSecondTerminalIso arithmeticZeroSecondTerminalSmoothing
    arithmeticZeroSecondTerminalFactor
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m
      (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroSecondTerminalIntegralField hπ data H j hj u hu)).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m
      (arithmeticFourthTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroSecondTerminalIntegralField hπ data H j hj u hu) b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m _ _ b)

end FLT.Mazur.WeierstrassDividedDepth
