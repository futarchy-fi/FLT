/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFirstResidualOrientation

/-!
# A complete first-order atlas with both residual closing transitions removed

Only the last retained node on each arm and the common terminal node are
corrected. All original labels remain in the open cover. The two smoothing
parameters remain distinct; the closing maps are their standard punctures.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "B" => changedArithmeticAtlasObject hπ data H 1 j hj u hu
local notation "κ" => changedArithmeticAtlasChart hπ data H 1 j hj u hu
local notation "I" => changedArithmeticAtlasIso hπ data H 1 j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H 1 j hj u hu
local notation "C" => arithmeticFirstResidualOrientedIso hπ data H j hj u hu
local notation "F" => arithmeticFirstResidualTerminalIso hπ data H j hj u hu

/-- The constructed full-chart correction, supported at the two closing pairs. -/
def arithmeticFirstResidualAtlasCorrection (i : ArithmeticChartLabel (j + 1)) : B i ≅ B i :=
  match i with
  | .terminal => F
  | .retained a b => if a.val = j then C b else Iso.refl _
  | .initial _ => Iso.refl _
  | .infinity => Iso.refl _

local notation "E" => arithmeticFirstResidualAtlasCorrection hπ data H j hj u hu

/-- The actual corrected chart inclusions in the one complete target. -/
def arithmeticFirstResidualAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    B i ⟶ simultaneousTwistedArithmeticStage hπ data H 1 j hj u hu :=
  (E i).inv ≫ κ i

instance arithmeticFirstResidualAtlasChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (arithmeticFirstResidualAtlasChart hπ data H j hj u hu i) := by
  unfold arithmeticFirstResidualAtlasChart
  infer_instance

/-- Every original chart has a constructed comparison to its corrected full chart. -/
def arithmeticFirstResidualAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H 1 (j + 1) hj i ≅ B i :=
  I i ≪≫ E i

local notation "c" => arithmeticLabeledAtlasMap hπ data H 1 (j + 1) hj
local notation "ι" => arithmeticFirstResidualAtlasChart hπ data H j hj u hu
local notation "J" => arithmeticFirstResidualAtlasIso hπ data H j hj u hu

/-- The full original chart inclusion is recovered after the two explicit corrections. -/
@[reassoc] theorem arithmeticFirstResidualAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ (G).hom = (J i).hom ≫ ι i := by
  rw [arithmeticFirstResidualAtlasIso, Iso.trans_hom, arithmeticFirstResidualAtlasChart,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact changedArithmeticAtlasIso_chart hπ data H 1 j hj u hu i

/-- All corrected full charts still cover the entire global target. -/
theorem arithmeticFirstResidualAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H 1 j hj u hu) :
    ∃ i x, ι i x = z := by
  obtain ⟨i, x, rfl⟩ := changedArithmeticAtlas_cover hπ data H 1 j hj u hu z
  refine ⟨i, (E i).hom x, ?_⟩
  exact congrArg (fun f ↦ f x) (by
    rw [arithmeticFirstResidualAtlasChart, Iso.hom_inv_id_assoc] :
      (E i).hom ≫ ι i = κ i)

/-- A full labeled open cover, with one shared corrected terminal node. -/
def arithmeticFirstResidualOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H 1 j hj u hu).OpenCover where
  I₀ := ArithmeticChartLabel (j + 1)
  X := B
  f := ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨arithmeticFirstResidualAtlas_cover hπ data H j hj u hu,
      fun i ↦ arithmeticFirstResidualAtlasChart_isOpenImmersion hπ data H j hj u hu i⟩

local notation "Q" => Quotient R π 1
local notation "σ" => arithmeticTerminalChangedSmoothing data H 1 j hj u hu
local notation "L" => arithmeticClosingRetainedBoundary data H 1
local notation "D" => arithmeticTerminalChangedBoundary data H 1 j hj u hu
local notation "O" => twistedRetainedOrientation data H 1
local notation "K" => arithmeticFirstResidualOverlapIso hπ data H j hj u hu

/-- Both closing equations now use the standard full punctures in this complete atlas. -/
@[reassoc] theorem arithmeticFirstResidualAtlas_closing (b : Bool) :
    L ≫ (O b).hom ≫ ι (.retained ⟨j, by omega⟩ b) =
      (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) ≫ ι .terminal := by
  have ht : (if b then leftBranchOpen Q σ else rightBranchOpen Q σ) ≫ (F).inv =
      (K b).inv ≫ D b := by
    apply (cancel_epi (K b).hom).mp
    rw [Iso.hom_inv_id_assoc, ← Category.assoc,
      ← arithmeticFirstResidualTerminal_square, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  simp only [arithmeticFirstResidualAtlasChart, arithmeticFirstResidualAtlasCorrection,
    ↓reduceIte]
  rw [← Category.assoc L, ← Category.assoc,
    arithmeticFirstResidualOrientedIso_closing_inv, Category.assoc, Category.assoc,
    changedArithmeticAtlas_closing, ← Category.assoc, ← ht, Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
