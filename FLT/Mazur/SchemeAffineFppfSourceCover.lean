/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeAffineFppfSourceChart

/-!
# Simultaneous source and base covers by descent charts

Choose one constructed source chart around each point of the original
cover. Their source opens cover that scheme; surjectivity of the fppf map
and the actual chart squares imply that their base opens cover the base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace FLT.Mazur.SchemeAffineDescent
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} (p : Y ⟶ X)
variable [Flat p] [Surjective p] [LocallyOfFinitePresentation p]

/-- One affine source neighborhood inside a descent chart for each original source point. -/
def fppfSourceCharts (y : Y) : SourceChart p := (exists_fppf_sourceChart p y).choose

/-- The chosen source chart contains its indexing point. -/
lemma fppfSourceCharts_mem (y : Y) : y ∈ Set.range (fppfSourceCharts p y).sourceMap :=
  (exists_fppf_sourceChart p y).choose_spec

/-- The actual source opens form a cover of the entire covering scheme. -/
theorem fppfSourceCharts_sourceCovers :
    iSup (fun y ↦ (fppfSourceCharts p y).sourceMap.opensRange) = ⊤ := by
  apply top_unique
  intro y _
  exact Opens.mem_iSup.mpr ⟨y, fppfSourceCharts_mem p y⟩

/-- The descent chart bases also cover, by surjectivity and the constructed squares. -/
theorem fppfSourceCharts_baseCovers :
    iSup (fun y ↦ (fppfSourceCharts p y).chart.base.opensRange) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨y, rfl⟩ := p.surjective x
  obtain ⟨z, hz⟩ := fppfSourceCharts_mem p y
  let C := fppfSourceCharts p y
  refine Opens.mem_iSup.mpr ⟨y, Spec.map C.chart.ringMap (C.lift z), ?_⟩
  change (Spec.map C.chart.ringMap ≫ C.chart.base) (C.lift z) = p y
  rw [C.chart.square]
  change p ((C.lift ≫ C.chart.cover) z) = p y
  rw [C.square]
  exact congrArg p hz

end FLT.Mazur.SchemeAffineDescent
