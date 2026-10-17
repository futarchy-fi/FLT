/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTerminalChangedSmoothing
public import FLT.Mazur.WeierstrassDividedTwistedClosingInclusion

/-!
# The changed terminal chart in the full labeled arithmetic target

Replace only the terminal chart in the already glued full target. All other
labels and comparisons remain the original ones. The exact revised closing
equations hold for both branches in this one global scheme.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m j : ℕ) (hj : j + 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨j + 1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "A" => twistedArithmeticAtlasObject hπ data H m j hj
local notation "e" => twistedArithmeticAtlasIso hπ data H m j hj u hu
local notation "G" => simultaneousTwistedArithmeticIso hπ data H m j hj u hu
local notation "ι" => simultaneousTwistedArithmeticChart hπ data H m j hj u hu
local notation "N" => arithmeticTerminalChangedIso data H m j hj u hu

/-- All original labels, with precisely the terminal object using the changed smoothing. -/
def changedArithmeticAtlasObject : ArithmeticChartLabel (j + 1) → Scheme
  | .terminal => PolygonSmoothing.chart (Quotient R π m)
      (arithmeticTerminalChangedSmoothing data H m j hj u hu)
  | i => A i

/-- The full chart comparison to the already constructed global atlas. -/
def changedArithmeticAtlasToTwisted (i : ArithmeticChartLabel (j + 1)) :
    changedArithmeticAtlasObject hπ data H m j hj u hu i ≅ A i :=
  match i with
  | .terminal => (N).symm
  | .retained _ _ => Iso.refl _
  | .infinity => Iso.refl _
  | .initial _ => Iso.refl _

local notation "J" => changedArithmeticAtlasToTwisted hπ data H m j hj u hu

/-- Every revised chart is embedded in the same complete glued target. -/
def changedArithmeticAtlasChart (i : ArithmeticChartLabel (j + 1)) :
    changedArithmeticAtlasObject hπ data H m j hj u hu i ⟶
      simultaneousTwistedArithmeticStage hπ data H m j hj u hu :=
  (J i).hom ≫ ι i

instance changedArithmeticAtlasChart_isOpenImmersion (i : ArithmeticChartLabel (j + 1)) :
    IsOpenImmersion (changedArithmeticAtlasChart hπ data H m j hj u hu i) := by
  unfold changedArithmeticAtlasChart
  infer_instance

/-- The source chart is unchanged and its full comparison uses the changed terminal chart. -/
def changedArithmeticAtlasIso (i : ArithmeticChartLabel (j + 1)) :
    arithmeticLabeledAtlasObject hπ data H m (j + 1) hj i ≅
      changedArithmeticAtlasObject hπ data H m j hj u hu i :=
  e i ≪≫ (J i).symm

local notation "c" => arithmeticLabeledAtlasMap hπ data H m (j + 1) hj
local notation "κ" => changedArithmeticAtlasChart hπ data H m j hj u hu
local notation "I" => changedArithmeticAtlasIso hπ data H m j hj u hu

/-- Every original labeled chart inclusion is preserved in the complete global comparison. -/
@[reassoc] theorem changedArithmeticAtlasIso_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ (G).hom = (I i).hom ≫ κ i := by
  rw [changedArithmeticAtlasIso, Iso.trans_hom, Iso.symm_hom,
    changedArithmeticAtlasChart, Category.assoc, Iso.inv_hom_id_assoc]
  exact simultaneousTwistedArithmeticIso_chart hπ data H m j hj u hu i

/-- Both closing equations hold with the actual original retained orientation and full residual. -/
@[reassoc] theorem changedArithmeticAtlas_closing (b : Bool) :
    arithmeticClosingRetainedBoundary data H m ≫
      (twistedRetainedOrientation data H m b).hom ≫ κ (.retained ⟨j, by omega⟩ b) =
        arithmeticTerminalChangedBoundary data H m j hj u hu b ≫ κ .terminal := by
  change _ ≫ _ ≫ (𝟙 _ ≫ _) = _ ≫ (N).inv ≫ _
  rw [Category.id_comp, ← arithmeticTerminalChangedBoundary_transport,
    Category.assoc, Iso.hom_inv_id_assoc]
  exact simultaneousTwistedClosing_boundary hπ data H m j hj u hu b

/-- The revised labeled charts cover the whole target, including the full terminal node. -/
theorem changedArithmeticAtlas_cover
    (z : simultaneousTwistedArithmeticStage hπ data H m j hj u hu) :
    ∃ i x, κ i x = z := by
  obtain ⟨i, x, hx⟩ := arithmeticLabeledAtlas_cover hπ data H m (j + 1) hj ((G).inv z)
  refine ⟨i, (I i).hom x, ?_⟩
  have he := congrArg (fun f ↦ f x) (changedArithmeticAtlasIso_chart hπ data H m j hj u hu i)
  change (G).hom (c i x) = κ i ((I i).hom x) at he
  rw [hx] at he
  exact he.symm.trans (congrArg (fun f ↦ f z) (G).inv_hom_id)

/-- A complete open cover with the revised terminal smoothing and all original labels. -/
def changedArithmeticOpenCover :
    (simultaneousTwistedArithmeticStage hπ data H m j hj u hu).OpenCover where
  I₀ := ArithmeticChartLabel (j + 1)
  X := changedArithmeticAtlasObject hπ data H m j hj u hu
  f := κ
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨changedArithmeticAtlas_cover hπ data H m j hj u hu,
      fun i ↦ changedArithmeticAtlasChart_isOpenImmersion hπ data H m j hj u hu i⟩

end FLT.Mazur.WeierstrassDividedDepth
