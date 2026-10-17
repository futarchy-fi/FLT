/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroFirstNodes
public import FLT.Mazur.WeierstrassModificationXArithmeticInitialNormalizedPuncture

/-!
# A full first correction of the original initial open chart

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
local notation "s" => arithmeticZeroFirstInitialSmoothing hπ data H j hj u hu m
/-- The initial open is transported by the entire first correction node. -/
def arithmeticZeroFirstInitialNodeIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q (s b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFirstInitialFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both punctures retain the actual whole initial correction. -/
@[reassoc] theorem arithmeticZeroFirstInitialNodeIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFirstInitialNodeIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (correctionPunctureFactor R π m τ
        (arithmeticZeroFirstInitialIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (s b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFirstInitialFactor_puncture hπ data H j hj u hu m b a

/-- The same last node changes its smoothing on both incident boundaries. -/
def arithmeticZeroFirstLastIso (b : Bool) :
    PolygonSmoothing.chart Q τ ≅ PolygonSmoothing.chart Q
      (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) :=
  Scheme.Spec.mapIso
    (arithmeticZeroFirstLastFactor hπ data H j hj u hu m b).toRingEquiv.toCommRingCatIso.op

/-- Both last punctures are induced by this one full node comparison. -/
@[reassoc] theorem arithmeticZeroFirstLastIso_puncture (b a : Bool) :
    punctureOpen τ a ≫ (arithmeticZeroFirstLastIso hπ data H m j hj u hu b).hom =
      (punctureSpecIso (twoBranchCorrectionPunctureFactor R π m τ
        (arithmeticZeroFirstLastIntegralField hπ data H j hj u hu b) a)).hom ≫
          punctureOpen (arithmeticZeroFirstLastSmoothing hπ data H j hj u hu m b) a := by
  apply punctureFactor_spec
  exact arithmeticZeroFirstLastFactor_puncture hπ data H j hj u hu m b a

local notation "C" => arithmeticZeroFirstInitialNodeIso hπ data H m j hj u hu
local notation "M" => arithmeticInitialMobiusChart W H.a1_unit (π ^ 1) π m
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π m W (π ^ 1) H.a1_unit H.scale_div
local notation "N" => arithmeticInitialNormalizedPunctureIso π m W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)
local notation "V" => arithmeticZeroFirstInitialIntegralField hπ data H j hj u hu
local notation "A" => fun b ↦ punctureSpecIso (correctionPunctureFactor R π m τ (V b) true)

/-- The actual initial open moved through the full first node correction. -/
def arithmeticZeroFirstInitialObject (b : Bool) : Scheme := pullback (C b).inv M

/-- The original initial chart is isomorphic to its constructed corrected open. -/
def arithmeticZeroFirstInitialIso (b : Bool) :
    Spec (.of (PolynomialNodeOpen (W.map (algebraMap R Q)) (algebraMap R Q (π ^ 1)))) ≅
      arithmeticZeroFirstInitialObject hπ data H m j hj u hu b :=
  (asIso (pullback.snd (C b).inv M)).symm

local notation "I" => arithmeticZeroFirstInitialIso hπ data H m j hj u hu

/-- The corrected initial open sits inside its full changed-smoothing node. -/
def arithmeticZeroFirstInitialNodeChart (b : Bool) :
    arithmeticZeroFirstInitialObject hπ data H m j hj u hu b ⟶ PolygonSmoothing.chart Q (s b) :=
  pullback.fst (C b).inv M

local notation "F" => arithmeticZeroFirstInitialNodeChart hπ data H m j hj u hu

instance arithmeticZeroFirstInitialNodeChart_isOpenImmersion (b : Bool) :
    IsOpenImmersion (F b) := by
  unfold arithmeticZeroFirstInitialNodeChart
  infer_instance

/-- The original full initial map is transported by the whole node factor. -/
@[reassoc] theorem arithmeticZeroFirstInitialIso_nodeChart (b : Bool) :
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
def arithmeticZeroFirstInitialPuncture (b : Bool) :
    branchTorus Q ⟶ arithmeticZeroFirstInitialObject hπ data H m j hj u hu b :=
  (A b).inv ≫ (N).inv ≫ P ≫ (I b).hom

/-- The constructed puncture is exactly the standard puncture of the changed node. -/
@[reassoc] theorem arithmeticZeroFirstInitialPuncture_nodeChart (b : Bool) :
    arithmeticZeroFirstInitialPuncture hπ data H m j hj u hu b ≫ F b =
      leftBranchOpen Q (s b) := by
  simp only [arithmeticZeroFirstInitialPuncture, Category.assoc,
    arithmeticZeroFirstInitialIso_nodeChart]
  rw [arithmeticInitialNormalizedPunctureIso_inv_boundary_assoc]
  have h := arithmeticZeroFirstInitialNodeIso_puncture hπ data H m j hj u hu b true
  simp only [punctureOpen_true] at h
  rw [h, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
