/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineUniversalComparison
public import FLT.Mazur.CyclicCharacteristicProductComparisonGluing

/-!
# Actual full universal comparisons on the glued parameter cover

Both global families are pullbacks of the original normalized curves. On each
chart, the varying universal comparison gives an isomorphism of their actual
pullbacks, with every base-map transport explicit.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)
local notation "P" => productComparisonScheme n b c
local notation "s" => productComparisonStructure n b c
local notation "C" => productComparisonCover n b c

/-- The original left family over the entire glued comparison parameter scheme. -/
def productComparisonLeftCurve : GeneralizedEllipticCurve P :=
  (normalizedCurve n b).baseChange (s ≫ prod.fst)

/-- The original right family over the entire glued comparison parameter scheme. -/
def productComparisonRightCurve : GeneralizedEllipticCurve P :=
  (normalizedCurve n c).baseChange (s ≫ prod.snd)

variable (U : (normalizedProduct n b c).affineOpens)
local notation "L" => productOpenLeft n b c U
local notation "R" => productOpenRight n b c U
local notation "t" => affineComparisonStructure n b c L R

/-- The left chart endpoint is the actual restriction of the global endpoint. -/
theorem productComparisonLeftChart_base : (C).f U ≫ (s ≫ prod.fst) = t ≫ L := by
  rw [← Category.assoc, productComparisonChart_structure]
  simp only [productOpenComparisonStructure, productOpenLeft, DirectedAffineSpectrum.chart,
    Category.assoc]

/-- The right chart endpoint is the actual restriction of the global endpoint. -/
theorem productComparisonRightChart_base : (C).f U ≫ (s ≫ prod.snd) = t ≫ R := by
  rw [← Category.assoc, productComparisonChart_structure]
  simp only [productOpenComparisonStructure, productOpenRight, DirectedAffineSpectrum.chart,
    Category.assoc]

/-- Identify the original left global family's chart with the full affine universal family. -/
def productComparisonLeftChartIso :
    (productComparisonLeftCurve n b c).baseChange ((C).f U) ≅
      ((normalizedCurve n b).baseChange L).baseChange t :=
  ((normalizedCurve n b).baseChangeCompIso (s ≫ prod.fst) ((C).f U)).symm ≪≫
    (normalizedCurve n b).baseChangeCompEqIso L t ((C).f U ≫ (s ≫ prod.fst))
      (productComparisonLeftChart_base n b c U)

/-- Identify the original right global family's chart with the full affine universal family. -/
def productComparisonRightChartIso :
    (productComparisonRightCurve n b c).baseChange ((C).f U) ≅
      ((normalizedCurve n c).baseChange R).baseChange t :=
  ((normalizedCurve n c).baseChangeCompIso (s ≫ prod.snd) ((C).f U)).symm ≪≫
    (normalizedCurve n c).baseChangeCompEqIso R t ((C).f U ≫ (s ≫ prod.snd))
      (productComparisonRightChart_base n b c U)

/-- The actual universal full comparison on each chart of the global parameter scheme. -/
def productUniversalChartComparison :
    (productComparisonLeftCurve n b c).baseChange ((C).f U) ≅
      (productComparisonRightCurve n b c).baseChange ((C).f U) :=
  productComparisonLeftChartIso n b c U ≪≫ affineUniversalComparison n b c L R ≪≫
    (productComparisonRightChartIso n b c U).symm

end FLT.Mazur.CyclicCharacteristicAtlas
