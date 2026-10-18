/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFifthNodes
public import FLT.Mazur.WeierstrassDividedZeroFourthGeometry

/-!
# Fifth geometry for the initial open and the shared last node

The full initial open is pulled through its fifth factor from its actual
fourth smoothing. The last full factor starts on that last node's fourth smoothing.
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
local notation "e" => arithmeticZeroFourthInitialSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticZeroFourthLastSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticZeroFifthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticZeroFifthLastIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its exact fourth smoothing to its fifth. -/
def arithmeticZeroFifthInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFifthInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The last node uses the simultaneous initial and incoming correction. -/
def arithmeticZeroFifthLastIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFifthLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticZeroFifthInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticZeroFifthInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFifthInitialFactor_puncture hπ data H j hj u hu m b a

/-- Both last punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticZeroFifthLastIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticZeroFifthLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticZeroFifthLastSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFifthLastFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticZeroFifthInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticZeroFourthInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the actual fourth initial open through the full fifth node comparison. -/
def arithmeticZeroFifthInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fourth initial open is isomorphic to the constructed fifth initial open. -/
def arithmeticZeroFifthInitialIso (b : Bool) :
    arithmeticZeroFourthInitialObject hπ data H m j hj u hu b ≅
      arithmeticZeroFifthInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticZeroFifthInitialIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticZeroFifthInitialNodeChart (b : Bool) :
    arithmeticZeroFifthInitialObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticZeroFifthInitialNodeChart hπ data H m j hj u hu

instance arithmeticZeroFifthInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroFifthInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual fourth and fifth node maps. -/
@[reassoc] theorem arithmeticZeroFifthInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the actual fourth puncture with the fifth initial substitution. -/
def arithmeticZeroFifthInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroFifthInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ arithmeticZeroFourthInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticZeroFifthInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroFifthInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticZeroFifthInitialSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticZeroFifthInitialPuncture, Category.assoc,
    arithmeticZeroFifthInitialIso_nodeChart]
  rw [arithmeticZeroFourthInitialPuncture_nodeChart_assoc]
  have h := arithmeticZeroFifthInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

/-- The common terminal is transported by the inverse of its full rebased factor. -/
def arithmeticZeroFifthTerminalIso :
    PolygonSmoothing.chart Q (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) ≅
      PolygonSmoothing.chart Q (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) :=
  (Scheme.Spec.mapIso
    (arithmeticZeroFifthTerminalFactor hπ data H j hj u hu m).toRingEquiv.toCommRingCatIso.op).symm

/-- Both inverse punctures are induced by this one full common terminal comparison. -/
@[reassoc] theorem arithmeticZeroFifthTerminalIso_puncture (b : Bool) :
    punctureOpen (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m) b ≫
        (arithmeticZeroFifthTerminalIso hπ data H m j hj u hu).hom =
      (punctureSpecIso (twoBranchCorrectionRebasedPunctureFactor R π m
        (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m)
        (arithmeticZeroFifthTerminalIntegralField hπ data H j hj u hu) b).symm).hom ≫
          punctureOpen (arithmeticZeroFifthTerminalSmoothing hπ data H j hj u hu m) b := by
  unfold arithmeticZeroFifthTerminalIso arithmeticZeroFifthTerminalSmoothing
    arithmeticZeroFifthTerminalFactor
  exact punctureFactor_spec _ _
    (twoBranchCorrectionRebasedFactor R π m
      (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroFifthTerminalIntegralField hπ data H j hj u hu)).symm
    (twoBranchCorrectionRebasedPunctureFactor R π m
      (arithmeticZeroFourthTerminalSmoothing hπ data H j hj u hu m)
      (arithmeticZeroFifthTerminalIntegralField hπ data H j hj u hu) b).symm b
    (twoBranchCorrectionRebasedFactor_symm_puncture R π m _ _ b)

end FLT.Mazur.WeierstrassDividedDepth
