/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedThirdEarlierIncoming
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNormalizedPuncture

/-!
# A full third correction of the original initial open chart

Pulling the original initial open through the full positive node factor
constructs its corrected open, with its actual new smoothing and puncture.
The retained-node orientation is absent from this original initial chart.
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
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "s" => arithmeticThirdEarlierSmoothing hπ data H j hj u hu m
local notation "C" => arithmeticThirdEarlierIso hπ data H m j hj u hu
local notation "M" => arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "N" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "V" => arithmeticThirdEarlierIntegralField hπ data H j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m τ (V b) true)

/-- The actual initial open moved through the full third node correction. -/
def arithmeticThirdInitialObject (b : Bool) : Scheme := pullback (C b).inv M

/-- The original initial chart is isomorphic to its constructed corrected open. -/
def arithmeticThirdInitialIso (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticThirdInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv M)).symm

local notation "I" => arithmeticThirdInitialIso hπ data H m j hj u hu

/-- The corrected initial open sits inside its full changed-smoothing node. -/
def arithmeticThirdInitialNodeChart (b : Bool) :
    arithmeticThirdInitialObject hπ data H m j hj u hu b ⟶ PolygonSmoothing.chart Q (s b) :=
  pullback.fst (C b).inv M

local notation "F" => arithmeticThirdInitialNodeChart hπ data H m j hj u hu

instance arithmeticThirdInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticThirdInitialNodeChart
  infer_instance

/-- The original full initial map is transported by the whole node factor. -/
@[reassoc] theorem arithmeticThirdInitialIso_nodeChart (b : Bool) :
    (I b).hom ≫ F b = M ≫ (C b).hom := by
  apply (cancel_mono (C b).inv).mp
  rw [Category.assoc]
  change (asIso (pullback.snd (C b).inv M)).inv ≫
    pullback.fst (C b).inv M ≫ (C b).inv = _
  rw [pullback.condition]
  have hi := (asIso (pullback.snd (C b).inv M)).inv_hom_id
  simpa only [asIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Category.id_comp] using
    congrArg (fun f ↦ f ≫ M) hi

/-- The full corrected puncture uses both the original parameter and the new positive factor. -/
def arithmeticThirdInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticThirdInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ (N).inv ≫ P ≫ (I b).hom

/-- The constructed puncture is exactly the standard puncture of the changed node. -/
@[reassoc] theorem arithmeticThirdInitialPuncture_nodeChart (b : Bool) :
    arithmeticThirdInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (s b) := by
  simp only [arithmeticThirdInitialPuncture, Category.assoc,
    arithmeticThirdInitialIso_nodeChart]
  rw [arithmeticInitialNormalizedPunctureIso_inv_boundary_assoc]
  have h := arithmeticThirdEarlierIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
