/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstResidualAtlasEdges

/-!
# Gluing the complete atlas after removing both first-order closing residuals

The original full overlaps and triple intersections are retained. Both
closing equations use standard punctures in this single glued scheme, and
every original chart participates in its constructed global comparison.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "𝒰" => arithmeticFirstResidualOpenCover hπ data H j hj u hu
local notation "c" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "J" => arithmeticFirstResidualAtlasIso hπ data H j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H 1 j hj u hu

/-- The actual full overlaps of the corrected cover, with their triple-overlap data. -/
def arithmeticFirstResidualGlueData : Scheme.GlueData := (𝒰).gluedCover

/-- One glued target contains both standard closing pairs and all original labels. -/
def arithmeticFirstResidualStage : Scheme :=
  (arithmeticFirstResidualGlueData hπ data H j hj u hu).glued

/-- The global comparison is constructed from the full corrected cover. -/
def arithmeticFirstResidualGlobalIso :
    finiteGlobalArithmeticStage hπ data (j + 1) hj 1 ≅
      arithmeticFirstResidualStage hπ data H j hj u hu :=
  G ≪≫ (asIso (𝒰).fromGlued).symm

/-- The full labeled chart inclusions into the simultaneous corrected gluing. -/
def arithmeticFirstResidualStageChart (i : ArithmeticChartLabel (j + 1)) :
    changedArithmeticAtlasObject hπ data H 1 j hj u hu i ⟶
      arithmeticFirstResidualStage hπ data H j hj u hu :=
  (arithmeticFirstResidualGlueData hπ data H j hj u hu).ι i

local notation "ι" => arithmeticFirstResidualStageChart hπ data H j hj u hu
local notation "E" => arithmeticFirstResidualGlobalIso hπ data H j hj u hu
local notation "κ" => arithmeticFirstResidualAtlasChart hπ data H j hj u hu

instance arithmeticFirstResidualStageChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) : IsOpenImmersion (ι i) := by
  unfold arithmeticFirstResidualStageChart
  infer_instance

/-- The new chart inclusion recovers its full corrected inclusion before gluing. -/
@[reassoc] theorem arithmeticFirstResidualStageChart_fromGlued
    (i : ArithmeticChartLabel (j + 1)) : ι i ≫ (𝒰).fromGlued = κ i :=
  (𝒰).ι_fromGlued i

/-- Every original full chart commutes with the single constructed global isomorphism. -/
@[reassoc] theorem arithmeticFirstResidualGlobalIso_chart
    (i : ArithmeticChartLabel (j + 1)) : c i ≫ (E).hom = (J i).hom ≫ ι i := by
  apply (cancel_mono (𝒰).fromGlued).mp
  rw [Category.assoc, arithmeticFirstResidualGlobalIso, Iso.trans_hom,
    Iso.symm_hom, Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id,
    Category.assoc, arithmeticFirstResidualStageChart_fromGlued]
  exact arithmeticFirstResidualAtlasIso_chart hπ data H j hj u hu i

/-- Every original full pair intersection is identified, not just its reduced points. -/
def arithmeticFirstResidualFullOverlapIso (a b : ArithmeticChartLabel (j + 1)) :
    pullback (c a) (c b) ≅ pullback (ι a) (ι b) :=
  asIso (pullback.map (c a) (c b) (ι a) (ι b) (J a).hom (J b).hom (E).hom
    (arithmeticFirstResidualGlobalIso_chart hπ data H j hj u hu a)
    (arithmeticFirstResidualGlobalIso_chart hπ data H j hj u hu b))

/-- The first projection retains its full original chart normalization. -/
@[reassoc] theorem arithmeticFirstResidualFullOverlapIso_fst (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticFirstResidualFullOverlapIso hπ data H j hj u hu a b).hom ≫
      pullback.fst (ι a) (ι b) = pullback.fst (c a) (c b) ≫ (J a).hom :=
  pullback.lift_fst _ _ _

/-- The second projection retains its full original chart normalization. -/
@[reassoc] theorem arithmeticFirstResidualFullOverlapIso_snd (a b : ArithmeticChartLabel (j + 1)) :
    (arithmeticFirstResidualFullOverlapIso hπ data H j hj u hu a b).hom ≫
      pullback.snd (ι a) (ι b) = pullback.snd (c a) (c b) ≫ (J b).hom :=
  pullback.lift_snd _ _ _

/-- The complete triple-overlap cocycle survives both closing corrections. -/
theorem arithmeticFirstResidualStage_cocycle (a b z : ArithmeticChartLabel (j + 1)) :
    (arithmeticFirstResidualGlueData hπ data H j hj u hu).t' a b z ≫
      (arithmeticFirstResidualGlueData hπ data H j hj u hu).t' b z a ≫
        (arithmeticFirstResidualGlueData hπ data H j hj u hu).t' z a b = 𝟙 _ :=
  (arithmeticFirstResidualGlueData hπ data H j hj u hu).cocycle a b z

local notation "Q" => Quotient R π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H 1
local notation "O" => twistedRetainedOrientation data H 1

/-- The one glued target satisfies both standard closing equations with one terminal chart. -/
@[reassoc] theorem arithmeticFirstResidualStage_closing (b : Bool) :
    L ≫ (O b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) ≫ ι .terminal := by
  apply (cancel_mono (𝒰).fromGlued).mp
  simp only [Category.assoc, arithmeticFirstResidualStageChart_fromGlued]
  exact arithmeticFirstResidualAtlas_closing hπ data H j hj u hu b

local notation "t" => parameter R π 1
local notation "I" => changedArithmeticAtlasIso hπ data H 1 j hj u hu

/-- The glued target retains every original adjacent arrow, including the last incoming one. -/
@[reassoc] theorem arithmeticFirstResidualStage_adjacent
    (a : ℕ) (ha : a + 1 < j + 1) (b : Bool) :
    (leftBranchOpen Q t ≫ (I (.retained ⟨a, by omega⟩ b)).hom) ≫
        ι (.retained ⟨a, by omega⟩ b) =
      (precedingBranch Q t ≫ (I (.retained ⟨a + 1, ha⟩ b)).hom) ≫
        ι (.retained ⟨a + 1, ha⟩ b) := by
  apply (cancel_mono (𝒰).fromGlued).mp
  simp only [Category.assoc, arithmeticFirstResidualStageChart_fromGlued]
  simpa only [Category.assoc] using
    arithmeticFirstResidualAtlas_adjacent hπ data H j hj u hu a ha b

local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "P" => arithmeticInitialPunctureInclusion π 1 W (π ^ 1) H.a1_unit H.scale_div
local notation "B" => arithmeticInitialPunctureIso π 1 W (π ^ 1)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) H.a1_unit H.scale_div H.a2_div
    (H.b3_div _) (H.b4_div _) (H.b6_div _)

/-- Both first edges in the glued scheme retain their entire original parameter. -/
@[reassoc] theorem arithmeticFirstResidualStage_initial (b : Bool) :
    P ≫ ι (.initial b) =
      ((B).inv ≫ rightBranchOpen Q t ≫
        (I (.retained ⟨0, Nat.zero_lt_succ j⟩ b)).hom) ≫
          ι (.retained ⟨0, Nat.zero_lt_succ j⟩ b) := by
  apply (cancel_mono (𝒰).fromGlued).mp
  simp only [Category.assoc, arithmeticFirstResidualStageChart_fromGlued]
  simpa only [Category.assoc] using arithmeticFirstResidualAtlas_initial hπ data H j hj u hu b

end FLT.Mazur.WeierstrassDividedDepth
