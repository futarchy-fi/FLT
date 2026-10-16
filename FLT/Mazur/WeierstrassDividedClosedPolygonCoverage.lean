/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedPolygonLabelCover
public import FLT.Mazur.WeierstrassDividedClosedPolygonDescent
public import FLT.Mazur.WeierstrassDividedClosedInfinityPolygonImage
public import FLT.Mazur.WeierstrassDividedArithmeticInitialPolygonImage

/-!
# Surjectivity of the complete original closed polygon comparison

Every prescribed polygon chart is covered by the original arithmetic labels.
For initial nodes the full infinity label fills precisely the missing edge;
retained and terminal nodes are covered by their whole-chart normalizations.
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
local notation "c" => @PolygonInfinitesimal.chart Q _ τ hn (2 * (j + 1) + 3)
  (Nat.le_trans (Nat.le_succ 2) (Nat.le_add_left 3 (2 * (j + 1))))
local notation "G" => arithmeticClosedPolygonComparisonChart hπ data H j hj u hu
local notation "F" => arithmeticClosedPolygonMap hπ data H j hj u hu
local notation "a" => arithmeticLabeledAtlasMap hπ data H 0 (j + 1) hj
local notation "e" => twistedArithmeticAtlasIso hπ data H 0 j hj u hu
local notation "N" => arithmeticClosedTerminalNormalization data H j hj u hu

/-- Every original chart comparison lands in the range of the descended map. -/
theorem arithmeticClosedPolygonComparisonChart_range_subset (i : ArithmeticChartLabel (j + 1)) :
    Set.range (G i) ⊆ Set.range F := by
  rintro _ ⟨x, rfl⟩
  refine ⟨a i x, ?_⟩
  exact congrArg (fun f ↦ f x) (arithmeticClosedPolygonMap_chart hπ data H j hj u hu i)

/-- Every retained normalized polygon node occurs in full in the original comparison image. -/
theorem arithmeticClosedPolygonMap_retained_range (idx : Fin (j + 1)) (b : Bool) :
    Set.range (c (retainedPolygonIndex (j + 1) idx b)) ⊆ Set.range F := by
  let _ := hn
  have hs : Function.Surjective (e (.retained idx b)).hom :=
    (Scheme.homeoOfIso (e (.retained idx b))).surjective
  have hr : Set.range (G (.retained idx b)) =
      Set.range (c (retainedPolygonIndex (j + 1) idx b)) := by
    change Set.range
      (arithmeticPolygonComparisonChart hπ data H 0 j hj u hu (.retained idx b)) = _
    rw [← twistedArithmeticRetained_polygon hπ data H 0 j hj u hu idx b]
    change Set.range ((c (retainedPolygonIndex (j + 1) idx b)) ∘
      (e (.retained idx b)).hom) = _
    rw [Set.range_comp, hs.range_eq, Set.image_univ]
  rw [← hr]
  exact arithmeticClosedPolygonComparisonChart_range_subset hπ data H j hj u hu _

/-- The simultaneous terminal normalization fills the entire original label zero. -/
theorem arithmeticClosedPolygonMap_terminal_range : Set.range (c 0) ⊆ Set.range F := by
  let _ := hn
  rintro _ ⟨x, rfl⟩
  apply arithmeticClosedPolygonComparisonChart_range_subset hπ data H j hj u hu .terminal
  refine ⟨((e .terminal) ≪≫ N).inv x, ?_⟩
  change (((e .terminal) ≪≫ N).inv ≫ ((e .terminal) ≪≫ N).hom ≫ c 0) x = _
  rw [Iso.inv_hom_id_assoc]

/-- The complete infinity edge is contained in the descended comparison image. -/
theorem arithmeticClosedPolygonMap_infinity_range :
    Set.range (rightBranchOpen Q τ ≫ c (initialPolygonIndex (j + 1) false)) ⊆
      Set.range F := by
  rw [← arithmeticClosedInfinityPolygonMap_range data H hπ (j + 1) hj]
  exact arithmeticClosedPolygonComparisonChart_range_subset hπ data H j hj u hu .infinity

/-- Each full initial polygon node is covered by its original label and the infinity label. -/
theorem arithmeticClosedPolygonMap_initial_range (b : Bool) :
    Set.range (c (initialPolygonIndex (j + 1) b)) ⊆ Set.range F := by
  let _ := hn
  let O : PolygonSmoothing.chart Q τ ⟶ PolygonSmoothing.chart Q τ :=
    if b then (branchSwapIso Q τ).hom else 𝟙 _
  have hs : Function.Surjective O := by
    cases b
    · exact Function.surjective_id
    · exact (Scheme.homeoOfIso (branchSwapIso Q τ)).surjective
  rintro _ ⟨x, rfl⟩
  obtain ⟨z, hz⟩ := hs x
  have hx := arithmeticFactorRatioLabeledInitialMap_edge_cover data H hπ 0 (j + 1) hj b z
  change c (initialPolygonIndex (j + 1) b) (O z) ∈
    Set.range (arithmeticFactorRatioLabeledInitialMap data H hπ 0 (j + 1) hj b) ∨
      c (initialPolygonIndex (j + 1) b) (O z) ∈
        Set.range (rightBranchOpen Q τ ≫ O ≫ c (initialPolygonIndex (j + 1) b)) at hx
  rw [hz] at hx
  rcases hx with hx | hx
  · exact arithmeticClosedPolygonComparisonChart_range_subset hπ data H j hj u hu
      (.initial b) hx
  · have hr := initialPolygon_infinity_edge_range Q τ (j + 1) b
    change Set.range (rightBranchOpen Q τ ≫ O ≫ c (initialPolygonIndex (j + 1) b)) = _ at hr
    rw [hr] at hx
    exact arithmeticClosedPolygonMap_infinity_range hπ data H j hj u hu hx

/-- All points of every polygon chart lie in the actual global comparison image. -/
theorem arithmeticClosedPolygonMap_chart_range (i : Fin (2 * (j + 1) + 3)) :
    Set.range (c i) ⊆ Set.range F := by
  rcases polygonIndex_cases (j + 1) i with rfl | ⟨b, rfl⟩ | ⟨idx, b, rfl⟩
  · exact arithmeticClosedPolygonMap_terminal_range hπ data H j hj u hu
  · exact arithmeticClosedPolygonMap_initial_range hπ data H j hj u hu b
  · exact arithmeticClosedPolygonMap_retained_range hπ data H j hj u hu idx b

/-- The complete descended comparison is surjective over the actual ring R/(pi). -/
theorem arithmeticClosedPolygonMap_surjective : Function.Surjective F := by
  let _ := hn
  intro x
  obtain ⟨i, y, rfl⟩ := PolygonInfinitesimal.charts_cover Q τ (2 * (j + 1) + 3) (by omega) x
  exact arithmeticClosedPolygonMap_chart_range hπ data H j hj u hu i ⟨y, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
