/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedClosedPolygonCoverage
public import Mathlib.AlgebraicGeometry.Morphisms.LocalIso

/-!
# Local isomorphism on the full original closed arithmetic stage

Every original chart comparison is an open immersion, including infinity
and the simultaneously corrected terminal chart. This proves the global
comparison is a local isomorphism; global injectivity is still required.
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
local notation "Q" => Quotient R π 0
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π 0
local notation "hn" => Fact.mk
  (arithmeticInitialFactorRatioSmoothing_nilpotent W H.a1_unit (π ^ 1) π 0 H.scale_div)
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu
local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu
local notation "U" => arithmeticLabeledOpenCover hπ data H 0 (j + 1) hj

/-- Every complete original chart embeds under its actual corrected comparison. -/
instance arithmeticClosedPolygonComparisonChart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) : IsOpenImmersion (G i) := by
  let _ := hn
  cases i with
  | infinity =>
    change IsOpenImmersion (arithmeticFactorRatioLabeledInfinityMap data H hπ 0 (j + 1) hj)
    infer_instance
  | initial b =>
    change IsOpenImmersion (arithmeticFactorRatioLabeledInitialMap data H hπ 0 (j + 1) hj b)
    infer_instance
  | retained idx b =>
    change IsOpenImmersion
      (arithmeticPolygonComparisonChart hπ data H 0 j hj u hu (.retained idx b))
    rw [← twistedArithmeticRetained_polygon hπ data H 0 j hj u hu idx b]
    infer_instance
  | terminal =>
    change IsOpenImmersion ((e .terminal).hom ≫ (N).hom ≫
      PolygonInfinitesimal.chart Q τ (2 * (j + 1) + 3) (by omega) 0)
    infer_instance

/-- The descended map is an open immersion on each member of the original full cover. -/
instance arithmeticClosedPolygonMap_chart_isOpenImmersion
    (i : ArithmeticChartLabel (j + 1)) : IsOpenImmersion (a i ≫ F) := by
  rw [arithmeticClosedPolygonMap_chart]
  infer_instance

/-- The actual original closed comparison is a Zariski local isomorphism. -/
instance arithmeticClosedPolygonMap_isLocalIso : IsLocalIso F := by
  rw [IsLocalIso.eq_sourceLocalClosure_isOpenImmersion]
  exact ⟨U, fun i ↦ arithmeticClosedPolygonMap_chart_isOpenImmersion hπ data H j hj u hu i⟩

/-- Only injectivity remains to promote the constructed local isomorphism to an embedding. -/
theorem arithmeticClosedPolygonMap_isOpenImmersion_of_injective (hi : Function.Injective F) :
    IsOpenImmersion F :=
  IsOpenImmersion.of_openCover_source F U hi
    (arithmeticClosedPolygonMap_chart_isOpenImmersion hπ data H j hj u hu)

/-- Surjectivity is already proved, so injectivity suffices for the actual polygon isomorphism. -/
theorem arithmeticClosedPolygonMap_isIso_of_injective (hi : Function.Injective F) : IsIso F := by
  let _ := arithmeticClosedPolygonMap_isOpenImmersion_of_injective hπ data H j hj u hu hi
  let _ : Epi (F).base := (TopCat.epi_iff_surjective _).mpr
    (arithmeticClosedPolygonMap_surjective hπ data H j hj u hu)
  exact IsOpenImmersion.isIso F

end FLT.Mazur.WeierstrassDividedDepth
