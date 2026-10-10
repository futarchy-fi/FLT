/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.BlowupReesGeneratorSpan
public import FLT.Mazur.BlowupReesProjChart

/-!
# The original center generators cover the actual Rees Proj

A family spanning the center gives both its degree-zero affine Proj cover
and its cover by the original fraction charts. These are the entire standard
opens, including exceptional points.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace.Opens

namespace FLT.Mazur.BlowupRees

universe u
variable {A : Type u} [CommRing A] (I : Ideal A)
  {ι : Type*} (g : ι → A) (hg : ∀ i, g i ∈ I)
  (hspan : Ideal.span (Set.range g) = I)

include hspan

/-- The original generator opens cover the actual projective spectrum. -/
theorem iSup_generatorOpen_eq_top : (⨆ i, generatorOpen I (g i) (hg i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (component I) (fun i => generator I (g i) (hg i))
    (irrelevant_eq_span_of_span I g hg hspan).le

/-- The degree-zero localizations at the original generators give an affine Proj cover. -/
def generatorAffineCover : (proj I).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan (component I)
    (fun i => generator I (g i) (hg i)) (fun i => generator_mem I (g i) (hg i))
    (fun _ => by decide : ∀ _ : ι, 0 < 1) (irrelevant_eq_span_of_span I g hg hspan).le

/-- Every Rees Proj point is in an original fraction chart. -/
theorem exists_fractionChart (z : proj I) :
    ∃ i p, fractionChartInclusion I (g i) (hg i) p = z := by
  have hz : z ∈ ⨆ i, generatorOpen I (g i) (hg i) := by
    rw [iSup_generatorOpen_eq_top I g hg hspan]
    trivial
  obtain ⟨i, hi⟩ := mem_iSup.mp hz
  rw [← fractionChartInclusion_range] at hi
  exact ⟨i, hi⟩

/-- The actual original fraction charts form an open cover of Rees Proj. -/
def fractionGeneratorCover : (proj I).OpenCover where
  I₀ := ι
  X i := Spec (.of (BlowupFractionChart.chart I (g i)))
  f i := fractionChartInclusion I (g i) (hg i)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨exists_fractionChart I g hg hspan, fun _ => inferInstance⟩

end FLT.Mazur.BlowupRees
