/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthShallowNodes
public import FLT.Mazur.WeierstrassDividedFourthShallowGeometry

/-!
# Fifth geometry for the original initial open and its neighbor

The full initial open is pulled through its fifth factor from its fourth
smoothing. Both endpoint factors retain their complete fourth inputs.
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
local notation "e" => arithmeticFourthShallowSmoothing hπ data H j hj u hu m
local notation "s" => arithmeticFourthShallowNeighborSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthShallowIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthShallowNeighborIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its fourth smoothing to its fifth. -/
def arithmeticFifthShallowNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthShallowFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The neighboring node uses the simultaneous initial and incoming correction. -/
def arithmeticFifthShallowNeighborIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticFifthShallowNeighborSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthShallowNeighborFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticFifthShallowNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticFifthShallowNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthShallowFactor_puncture hπ data H j hj u hu m b a

/-- Both neighboring punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticFifthShallowNeighborIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticFifthShallowNeighborIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticFifthShallowNeighborSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthShallowNeighborFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticFifthShallowNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticFourthShallowNodeChart hπ data H m j hj u hu
local notation "U" => arithmeticFourthShallowPuncture hπ data H m j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the fourth initial open through the full fifth node comparison. -/
def arithmeticFifthShallowObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The fourth initial open is isomorphic to the constructed fifth initial open. -/
def arithmeticFifthShallowIso (b : Bool) :
    arithmeticFourthShallowObject hπ data H m j hj u hu b ≅
      arithmeticFifthShallowObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticFifthShallowIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticFifthShallowNodeChart (b : Bool) :
    arithmeticFifthShallowObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticFifthShallowNodeChart hπ data H m j hj u hu

instance arithmeticFifthShallowNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticFifthShallowNodeChart
  infer_instance

/-- The full initial comparison commutes with its fourth and fifth node maps. -/
@[reassoc] theorem arithmeticFifthShallowIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the fourth corrected puncture with the fifth initial substitution. -/
def arithmeticFifthShallowPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticFifthShallowObject hπ data H m j hj u hu b :=
  (A b).inv ≫ U b ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticFifthShallowPuncture_nodeChart (b : Bool) :
    arithmeticFifthShallowPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticFifthShallowSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticFifthShallowPuncture, Category.assoc,
    arithmeticFifthShallowIso_nodeChart]
  rw [arithmeticFourthShallowPuncture_nodeChart_assoc]
  have h := arithmeticFifthShallowNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
