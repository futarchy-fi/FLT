/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroThirdNodes
public import FLT.Mazur.WeierstrassDividedZeroSecondGeometry

/-!
# Third geometry for the initial open and the shared last node

The full initial open is pulled through its third factor from its actual
second smoothing. The last full factor starts on that last node's second smoothing.
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
local notation "e" => arithmeticZeroSecondInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroSecondLastSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticZeroThirdInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticZeroThirdLastIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its exact second smoothing to its third. -/
def arithmeticZeroThirdInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroThirdInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticZeroThirdLastIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroThirdLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticZeroThirdInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticZeroThirdInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroThirdInitialFactor_puncture hπ data H j hj u hu m b a

/-- Both last punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticZeroThirdLastIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticZeroThirdLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroThirdLastFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticZeroThirdInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticZeroSecondInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the actual second initial open through the full third node comparison. -/
def arithmeticZeroThirdInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The second initial open is isomorphic to the constructed third initial open. -/
def arithmeticZeroThirdInitialIso (b : Bool) :
    arithmeticZeroSecondInitialObject hπ data H m j hj u hu b ≅
      arithmeticZeroThirdInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticZeroThirdInitialIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticZeroThirdInitialNodeChart (b : Bool) :
    arithmeticZeroThirdInitialObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticZeroThirdInitialNodeChart hπ data H m j hj u hu

instance arithmeticZeroThirdInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroThirdInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual second and third node maps. -/
@[reassoc] theorem arithmeticZeroThirdInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the actual second puncture with the third initial substitution. -/
def arithmeticZeroThirdInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroThirdInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ arithmeticZeroSecondInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticZeroThirdInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroThirdInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticZeroThirdInitialPuncture, Category.assoc,
    arithmeticZeroThirdInitialIso_nodeChart]
  rw [arithmeticZeroSecondInitialPuncture_nodeChart_assoc]
  have h := arithmeticZeroThirdInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticZeroThirdTerminalIso :
    PolygonSmoothing.chart Q (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) ≅
      PolygonSmoothing.chart Q (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticZeroThirdTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures are induced by this one full common terminal comparison. -/
@[reassoc] theorem arithmeticZeroThirdTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m) b ≫
        (arithmeticZeroThirdTerminalIso hπ data H m j hj u hu).hom =
      (punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
        (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m)
        (arithmeticZeroThirdTerminalIntegralField hπ data H j hj u hu) b).symm).hom ≫
          punctureOpen (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) b := by
  unfold arithmeticZeroThirdTerminalIso arithmeticZeroThirdTerminalSmoothing
    arithmeticZeroThirdTerminalFactor
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m
      (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroThirdTerminalIntegralField hπ data H j hj u hu)).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m
      (arithmeticZeroSecondTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroThirdTerminalIntegralField hπ data H j hj u hu) b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m _ _ b)

end FLT.Mazur.WeierstrassDividedDepth
