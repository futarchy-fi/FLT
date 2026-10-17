/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFifthFartherNodes
public import FLT.Mazur.WeierstrassDividedThirdInitialGeometry

/-!
# Fifth geometry for the original initial open and its neighbor

The full initial open is pulled through its fifth factor from its original
smoothing. The neighboring full factor starts on that neighbor's fourth smoothing.
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
local notation "e" => fun (_ : Bool) ↦
  arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticFourthFartherSmoothing hπ data H j hj u hu m
local notation "V" => arithmeticFifthFartherIntegralField hπ data H j hj u hu
local notation "P" => arithmeticFifthFartherNeighborIntegralField hπ data H j hj u hu

/-- The whole initial node changes from its original smoothing to its fifth. -/
def arithmeticFifthFartherNodeIso (b : Bool) :
    PolygonSmoothing.chart Q (e b) ≅
      PolygonSmoothing.chart Q (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthFartherFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- The neighboring node uses the simultaneous initial and incoming correction. -/
def arithmeticFifthFartherNeighborIso (b : Bool) :
    PolygonSmoothing.chart Q (s b) ≅ PolygonSmoothing.chart Q
      (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticFifthFartherNeighborFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both initial punctures are induced by the same whole node factor. -/
@[reassoc] theorem arithmeticFifthFartherNodeIso_puncture (b a : Bool) :
    punctureOpen (e b) a ≫ (arithmeticFifthFartherNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) a)).hom ≫
        punctureOpen (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthFartherFactor_puncture hπ data H j hj u hu m b a

/-- Both neighboring punctures retain their full simultaneous correction. -/
@[reassoc] theorem arithmeticFifthFartherNeighborIso_puncture (b a : Bool) :
    punctureOpen (s b) a ≫ (arithmeticFifthFartherNeighborIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m (s b) (P b) a)).hom ≫
        punctureOpen (arithmeticFifthFartherNeighborSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticFifthFartherNeighborFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticFifthFartherNodeIso hπ data H m j hj u hu
local notation "M" => fun (_ : Bool) ↦ arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "U" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "N" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m (e b) (V b) true)

/-- Pull the original initial open through the full fifth node comparison. -/
def arithmeticFifthFartherObject (b : Bool) : Scheme := pullback (C b).inv (M b)

/-- The original initial open is isomorphic to the constructed fifth initial open. -/
def arithmeticFifthFartherIso (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticFifthFartherObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv (M b))).symm

local notation "I" => arithmeticFifthFartherIso hπ data H m j hj u hu

/-- The corrected initial open maps into its full changed-smoothing node. -/
def arithmeticFifthFartherNodeChart (b : Bool) :
    arithmeticFifthFartherObject hπ data H m j hj u hu b ⟶
      PolygonSmoothing.chart Q (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) :=
  pullback.fst (C b).inv (M b)

local notation "F" => arithmeticFifthFartherNodeChart hπ data H m j hj u hu

instance arithmeticFifthFartherNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticFifthFartherNodeChart
  infer_instance

/-- The full initial comparison commutes with its original and fifth node maps. -/
@[reassoc] theorem arithmeticFifthFartherIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M b ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv (M b))).inv ≫
    pullback.fst (C b).inv (M b) ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv (M b))).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using congrArg (fun f ↦ f ≫ M b) hi

/-- Transport the original normalized puncture with the fifth initial substitution. -/
def arithmeticFifthFartherPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticFifthFartherObject hπ data H m j hj u hu b :=
  (A b).inv ≫ (N).inv ≫ U ≫ (I b).hom

/-- The puncture of the corrected initial open is the standard puncture of its new node. -/
@[reassoc] theorem arithmeticFifthFartherPuncture_nodeChart (b : Bool) :
    arithmeticFifthFartherPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (arithmeticFifthFartherSmoothing hπ data H j hj u hu m b) := by
  simp only [arithmeticFifthFartherPuncture, Category.assoc,
    arithmeticFifthFartherIso_nodeChart]
  rw [arithmeticInitialNormalizedPunctureIso_inv_boundary_assoc]
  have h := arithmeticFifthFartherNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
