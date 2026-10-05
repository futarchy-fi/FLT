/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntersectionGluingCharts
public import FLT.Mazur.OpenImmersionSectionComparison

/-!
# Ambient sections on glued intersection charts

Chart images cover the colimit. Union labels describe actual intersections,
and the section comparison commutes with every diagram restriction.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {ι : Type v} [Finite ι]
  (F : (NonemptyChartSet ι)ᵒᵖ ⥤ Scheme.{u})
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
  [(F ⋙ Scheme.forget).IsLocallyDirected]

/-- The actual open image of a chart in the scheme colimit. -/
def intersectionColimitOpen (s : NonemptyChartSet ι) : (colimit F).Opens :=
  (colimit.ι F (.op s)).opensRange

/-- Adding labels shrinks the corresponding colimit chart. -/
theorem intersectionColimitOpen_antitone : Antitone (intersectionColimitOpen F) := by
  intro s t h
  exact openImage_le_of_comp _ _ (F.map (homOfLE h).op) (colimit.w F _)

/-- Union labels give the actual intersection open. -/
@[simp] theorem intersectionColimitOpen_union (s t : NonemptyChartSet ι) :
    intersectionColimitOpen F (unionChartSet s t) =
      intersectionColimitOpen F s ⊓ intersectionColimitOpen F t :=
  TopologicalSpace.Opens.ext (intersection_colimit_range F s t)

/-- All intersection charts cover the scheme colimit. -/
theorem intersectionColimitOpen_cover : (⨆ s, intersectionColimitOpen F s) = ⊤ := by
  have h := (Scheme.IsLocallyDirected.openCover F).iSup_opensRange
  apply top_unique
  rw [← h]
  exact iSup_le fun i ↦ le_iSup (intersectionColimitOpen F) i.unop

/-- Global chart sections are ambient sections on its image. -/
def intersectionColimitSectionIso (s : NonemptyChartSet ι) :
    Γ(F.obj (.op s), ⊤) ≅ Γ(colimit F, intersectionColimitOpen F s) :=
  IsOpenImmersion.ΓIsoTop (colimit.ι F (.op s))

/-- Diagram restriction agrees with restriction of ambient sections. -/
theorem intersectionColimitSectionIso_naturality {s t : NonemptyChartSet ι}
    (h : s ≤ t) :
    (intersectionColimitSectionIso F s).hom ≫
        (colimit F).presheaf.map (homOfLE (intersectionColimitOpen_antitone F h)).op =
      (F.map (homOfLE h).op).appTop ≫ (intersectionColimitSectionIso F t).hom :=
  openImageSectionIso_naturality _ _ _ (colimit.w F _)

/-- Sections of a union chart are sections on the actual overlap of chart images. -/
def intersectionColimitOverlapSectionIso (s t : NonemptyChartSet ι) :
    Γ(F.obj (.op (unionChartSet s t)), ⊤) ≅
      Γ(colimit F, intersectionColimitOpen F s ⊓ intersectionColimitOpen F t) :=
  intersectionColimitSectionIso F (unionChartSet s t) ≪≫
    (colimit F).presheaf.mapIso (eqToIso (intersectionColimitOpen_union F s t).symm).op

/-- Every intersection chart is contained in any one of its singleton charts. -/
theorem intersectionColimitOpen_le_singleton (s : NonemptyChartSet ι)
    (i : ι) (hi : i ∈ s.val) :
    intersectionColimitOpen F s ≤ intersectionColimitOpen F (singletonChartSet i) :=
  intersectionColimitOpen_antitone F (Finset.singleton_subset_iff.mpr hi)

/-- The original singleton charts already cover the scheme colimit. -/
theorem intersectionColimitOpen_singleton_cover :
    (⨆ i, intersectionColimitOpen F (singletonChartSet i)) = ⊤ := by
  rw [← top_le_iff, ← intersectionColimitOpen_cover F]
  refine iSup_le fun s ↦ ?_
  obtain ⟨i, hi⟩ := s.property
  exact (intersectionColimitOpen_le_singleton F s i hi).trans
    (le_iSup (fun j : ι ↦ intersectionColimitOpen F (singletonChartSet j)) i)

end FLT.Mazur.Approximation
