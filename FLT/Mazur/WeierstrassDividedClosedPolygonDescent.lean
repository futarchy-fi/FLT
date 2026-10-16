/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedPolygonCompatibility
public import FLT.Mazur.WeierstrassDividedArithmeticPositiveLabeledDescent
public import FLT.Mazur.WeierstrassDividedTwistedAtlasRestriction

/-!
# An actual polygon comparison from the complete closed arithmetic model

The constructed compatible family descends on the original global cover.
Its restriction is exactly the previous exterior comparison, and transport
provides a map from the complete simultaneous twisted closed stage as well.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
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
local notation "Y" => arithmeticFactorRatioPolygon π 0 W (π ^ 1)
  H.a1_unit H.scale_div (j + 1)
local notation "c" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu

/-- The complete original closed stage has a constructed polygon comparison. -/
def arithmeticClosedPolygonMap : finiteGlobalArithmeticStage hπ data (j + 1) hj 0 ⟶ Y :=
  arithmeticPositiveLabeledDesc hπ data H 0 j hj G
    (arithmeticClosedPolygonComparisonChart_infinity hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_initial hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_adjacent hπ data H j hj u hu)
    (arithmeticClosedPolygonComparisonChart_terminalCompatible hπ data H j hj u hu)

/-- Every original full labeled chart is recovered by the descended comparison. -/
@[reassoc] theorem arithmeticClosedPolygonMap_chart (i : ArithmeticChartLabel (j + 1)) :
    c i ≫ arithmeticClosedPolygonMap hπ data H j hj u hu = G i :=
  arithmeticPositiveLabeledDesc_chart ..

/-- The original full chart restrictions uniquely characterize the global comparison. -/
theorem arithmeticClosedPolygonMap_unique
    (f : finiteGlobalArithmeticStage hπ data (j + 1) hj 0 ⟶ Y)
    (hf : ∀ i, c i ≫ f = G i) : f = arithmeticClosedPolygonMap hπ data H j hj u hu := by
  apply arithmeticPositiveLabeled_hom_ext hπ data H 0 j hj
  intro i
  rw [hf, arithmeticClosedPolygonMap_chart]

omit [IsBezout R] in
/-- All original exterior chart comparisons are preserved exactly. -/
theorem arithmeticClosedPolygonComparisonChart_exterior (i : ArithmeticExteriorLabel (j + 1)) :
    G i.val = arithmeticPolygonComparisonChart hπ data H 0 j hj u hu i.val := by
  obtain ⟨i, hi⟩ := i
  cases i <;> first | rfl | exact (hi rfl).elim

/-- The global comparison extends the entire previously constructed original exterior map. -/
@[reassoc] theorem arithmeticClosedPolygonMap_exterior :
    (arithmeticPolygonExterior hπ data H 0 j hj).ι ≫
        arithmeticClosedPolygonMap hπ data H j hj u hu =
      arithmeticPolygonExteriorMap hπ data H 0 j hj u hu := by
  apply openImageUnion_hom_ext (fun i : ArithmeticExteriorLabel (j + 1) ↦ c i.val)
  intro i
  dsimp only [arithmeticPolygonExterior]
  rw [openImageUnionMap_fac_assoc, arithmeticClosedPolygonMap_chart,
    arithmeticPolygonExteriorMap_chart, arithmeticClosedPolygonComparisonChart_exterior]

local notation "I" => simultaneousTwistedArithmeticIso hπ data H 0 j hj u hu
local notation "ι" => simultaneousTwistedArithmeticChart hπ data H 0 j hj u hu
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu

/-- The complete simultaneous twisted closed target now maps to the prescribed polygon. -/
def twistedArithmeticClosedPolygonMap :
    simultaneousTwistedArithmeticStage hπ data H 0 j hj u hu ⟶ Y :=
  (I).inv ≫ arithmeticClosedPolygonMap hπ data H j hj u hu

/-- The twisted comparison recovers the same original global comparison. -/
@[reassoc] theorem twistedArithmeticClosedPolygonMap_original :
    (I).hom ≫ twistedArithmeticClosedPolygonMap hπ data H j hj u hu =
      arithmeticClosedPolygonMap hπ data H j hj u hu := by
  rw [twistedArithmeticClosedPolygonMap, Iso.hom_inv_id_assoc]

/-- All normalized charts retain their actual constructed comparison formulas. -/
@[reassoc] theorem twistedArithmeticClosedPolygonMap_chart (i : ArithmeticChartLabel (j + 1)) :
    ι i ≫ twistedArithmeticClosedPolygonMap hπ data H j hj u hu = (e i).inv ≫ G i := by
  apply (cancel_epi (e i).hom).mp
  rw [← Category.assoc, ← simultaneousTwistedArithmeticIso_chart,
    Category.assoc, twistedArithmeticClosedPolygonMap_original,
    arithmeticClosedPolygonMap_chart, Iso.hom_inv_id_assoc]

local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)

/-- Each normalized retained chart still has precisely its prescribed polygon label. -/
@[reassoc] theorem twistedArithmeticClosedPolygonMap_retained (idx : Fin (j + 1)) (b : Bool) :
    let _ := hn
    ι (.retained idx b) ≫ twistedArithmeticClosedPolygonMap hπ data H j hj u hu =
      PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega)
        (retainedPolygonIndex (j + 1) idx b) := by
  let _ := hn
  rw [twistedArithmeticClosedPolygonMap_chart]
  change (e (.retained idx b)).inv ≫
    arithmeticPolygonComparisonChart hπ data H 0 j hj u hu (.retained idx b) = _
  rw [← twistedArithmeticRetained_polygon, Iso.inv_hom_id_assoc]

/-- The one terminal chart uses the simultaneous correction followed by polygon label zero. -/
@[reassoc] theorem twistedArithmeticClosedPolygonMap_terminal :
    let _ := hn
    ι .terminal ≫ twistedArithmeticClosedPolygonMap hπ data H j hj u hu =
      (arithmeticClosedTerminalNormalization data H j hj u hu).hom ≫
        PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0 := by
  let _ := hn
  rw [twistedArithmeticClosedPolygonMap_chart]
  change (e .terminal).inv ≫ (e .terminal).hom ≫ _ = _
  rw [Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
