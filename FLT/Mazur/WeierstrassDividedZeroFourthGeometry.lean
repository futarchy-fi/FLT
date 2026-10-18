/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFourthNodes
public import FLT.Mazur.WeierstrassDividedZeroThirdGeometry

/-!
# Fourth geometry for the initial open and the shared last node

The full initial open is pulled through its fourth factor from its actual
third smoothing. The last full factor starts on that last node's third smoothing.
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
local notation "e" => arithmeticZeroThirdInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroThirdLastSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticZeroFourthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticZeroFourthLastIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its exact third smoothing to its fourth. -/
def arithmeticZeroFourthInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFourthInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticZeroFourthLastIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFourthLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticZeroFourthInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticZeroFourthInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFourthInitialFactor_puncture hπ data H j hj u hu m b a

/-- Both last punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticZeroFourthLastIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticZeroFourthLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFourthLastFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticZeroFourthInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticZeroThirdInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the actual third initial open through the full fourth node comparison. -/
def arithmeticZeroFourthInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The third initial open is isomorphic to the constructed fourth initial open. -/
def arithmeticZeroFourthInitialIso (b : Bool) :
    arithmeticZeroThirdInitialObject hπ data H m j hj u hu b ≅
      arithmeticZeroFourthInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticZeroFourthInitialIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticZeroFourthInitialNodeChart (b : Bool) :
    arithmeticZeroFourthInitialObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticZeroFourthInitialNodeChart hπ data H m j hj u hu

instance arithmeticZeroFourthInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroFourthInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual third and fourth node maps. -/
@[reassoc] theorem arithmeticZeroFourthInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the actual third puncture with the fourth initial substitution. -/
def arithmeticZeroFourthInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroFourthInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ arithmeticZeroThirdInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticZeroFourthInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroFourthInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticZeroFourthInitialPuncture, Category.assoc,
    arithmeticZeroFourthInitialIso_nodeChart]
  rw [arithmeticZeroThirdInitialPuncture_nodeChart_assoc]
  have h := arithmeticZeroFourthInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticZeroFourthTerminalIso :
    PolygonSmoothing.chart Q (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) ≅
      PolygonSmoothing.chart Q (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticZeroFourthTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures are induced by this one full common terminal comparison. -/
@[reassoc] theorem arithmeticZeroFourthTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m) b ≫
        (arithmeticZeroFourthTerminalIso hπ data H m j hj u hu).hom =
      (punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
        (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m)
        (arithmeticZeroFourthTerminalIntegralField hπ data H j hj u hu) b).symm).hom ≫
          punctureOpen (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) b := by
  unfold arithmeticZeroFourthTerminalIso arithmeticZeroFourthTerminalSmoothing
    arithmeticZeroFourthTerminalFactor
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m
      (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroFourthTerminalIntegralField hπ data H j hj u hu)).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m
      (arithmeticZeroThirdTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroFourthTerminalIntegralField hπ data H j hj u hu) b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m _ _ b)

end FLT.Mazur.WeierstrassDividedDepth
