/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineFppfChartThrough

/-!
# Source open neighborhoods inside affine descent charts

Every point of an actual fppf cover has an affine open neighborhood that
factors through a faithfully flat descent chart by an open immersion.
The data records only schemes, maps, and their geometric properties.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- An original source open lying inside an affine faithfully flat descent chart. -/
structure SourceChart where
  /-- The faithfully flat affine descent square. -/
  chart : Chart p
  /-- An affine source neighborhood. -/
  source : Scheme.{u}
  /-- The neighborhood is affine. -/
  source_affine : IsAffine source
  /-- Its original map into the covering scheme. -/
  sourceMap : source ⟶ Y
  /-- The source map is an open immersion. -/
  source_open : IsOpenImmersion sourceMap
  /-- Its inclusion into the covering spectrum of the descent chart. -/
  lift : source ⟶ Spec chart.coverRing
  /-- This inclusion is an open immersion. -/
  lift_open : IsOpenImmersion lift
  /-- The original source map is retained. -/
  square : lift ≫ chart.cover = sourceMap
  /-- The descent chart has an open base. -/
  base_open : IsOpenImmersion chart.base

attribute [instance] SourceChart.source_affine SourceChart.source_open
  SourceChart.lift_open SourceChart.base_open

variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- Actual fppf geometry constructs a source chart around every point of the cover. -/
theorem exists_fppf_sourceChart (y : Y) :
    ∃ C : SourceChart p, y ∈ Set.range C.sourceMap := by
  obtain ⟨R, a, ha, x, hx⟩ := Scheme.exists_Spec_apply_eq (p y)
  let := ha
  have hy : y ∈ p ⁻¹ᵁ a.opensRange := ⟨x, hx⟩
  obtain ⟨V, hV, hyV, hsub⟩ := exists_isAffineOpen_mem_and_subset hy
  let : IsAffine V.toScheme := hV
  have hv : Set.range (V.ι ≫ p) ⊆ Set.range a := by
    rintro z ⟨t, rfl⟩
    exact hsub t.property
  let r := IsOpenImmersion.lift a (V.ι ≫ p) hv
  have hr : V.ι ≫ p = r ≫ a := (IsOpenImmersion.lift_fac a (V.ι ≫ p) hv).symm
  obtain ⟨C, t, hC, ht, htv⟩ := exists_fppf_chart_through p a V.ι r hr
  exact ⟨⟨C, V.toScheme, inferInstance, V.ι, inferInstance, t, ht, htv, hC⟩,
    ⟨⟨y, hyV⟩, rfl⟩⟩

end FLT.Mazur.SchemeAffineDescent
