/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthInitialNodes
public import FLT.Mazur.WeierstrassDividedThirdInitialGeometry

/-!
# Fourth geometry for the original initial open and its neighbor

The full initial open is pulled through its fourth factor from its actual
third smoothing. The neighboring full factor starts on that neighbor's third smoothing.
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
local notation "e" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticThirdPrecedingSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFourthInitialIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFourthInitialNeighborIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its exact third smoothing to its fourth. -/
def arithmeticFourthInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The neighboring node uses the simultaneous initial and incoming correction. -/
def arithmeticFourthInitialNeighborIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFourthInitialNeighborFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticFourthInitialNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticFourthInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthInitialFactor_puncture hπ data H j hj u hu m b a

/-- Both neighboring punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticFourthInitialNeighborIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticFourthInitialNeighborIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticFourthInitialNeighborSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFourthInitialNeighborFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticFourthInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticThirdInitialNodeChart hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the actual third initial open through the full fourth node comparison. -/
def arithmeticFourthInitialObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The third initial open is isomorphic to the constructed fourth initial open. -/
def arithmeticFourthInitialIso (b : Bool) :
    arithmeticThirdInitialObject hπ data H m j hj u hu b ≅
      arithmeticFourthInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticFourthInitialIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticFourthInitialNodeChart (b : Bool) :
    arithmeticFourthInitialObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticFourthInitialNodeChart hπ data H m j hj u hu

instance arithmeticFourthInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticFourthInitialNodeChart
  infer_instance

/-- The full initial comparison commutes with its actual third and fourth node maps. -/
@[reassoc] theorem arithmeticFourthInitialIso_nodeChart (b : Bool) :
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
def arithmeticFourthInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticFourthInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ arithmeticThirdInitialPuncture hπ data H m j hj u hu b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticFourthInitialPuncture_nodeChart (b : Bool) :
    arithmeticFourthInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticFourthInitialSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticFourthInitialPuncture, Category.assoc,
    arithmeticFourthInitialIso_nodeChart]
  rw [arithmeticThirdInitialPuncture_nodeChart_assoc]
  have h := arithmeticFourthInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
