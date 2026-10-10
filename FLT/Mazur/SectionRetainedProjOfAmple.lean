/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionRetainedChartMorphism
public import FLT.Mazur.SectionRetainedProjOpens

/-!
# Ampleness gives an open immersion into the retained Proj

The original affine generator charts are the retained homogeneous charts.
Their exact generator-open inverse images prove global injectivity and
hence the open-immersion property for the constructed canonical map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.SectionRetainedProjOfAmple

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover
open SectionRetainedChartComparison SectionRetainedChartMorphism
open SectionRetainedProjConstruction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

/-- The retained canonical map is an open immersion on every original affine generator chart. -/
theorem chart_isOpenImmersion (h : PositivePowerGenerated L q) {ι : Type*} [Finite ι]
    (d : ℕ) (s : ι → Γ(tensorPower L (q * d), ⊤)) (hd : 0 < d)
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤) (i : ι) :
    IsOpenImmersion ((chart s i).ι ≫ toProj L q h) := by
  rw [← toProjOn_eq L q d (s i) hd h (chart s i) le_rfl]
  have : IsIso (CommRingCat.ofHom (toFunctions L q d (s i) (chart s i) le_rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ringEquiv L q d s haff hcover i).bijective
  have : IsIso (chart s i).toSpecΓ := by
    rw [← (haff i).isoSpec_hom]
    infer_instance
  unfold toProjOn
  infer_instance

/-- Ampleness embeds the original scheme openly into its positive retained section-ring Proj. -/
theorem isOpenImmersion (hq : 0 < q) (hA : AmpleLineBundle L)
    (h : PositivePowerGenerated L q) : IsOpenImmersion (toProj L q h) := by
  obtain ⟨ι, hι, d, hd, s, haff, hcover⟩ := hA.retained_section_cover q hq
  let := hι
  have hi (i : ι) := chart_isOpenImmersion L q h d s hd haff hcover i
  have hinj : Function.Injective (toProj L q h) := by
    intro x y hxy
    have hx : x ∈ ⨆ i, chart s i := by rw [hcover]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hopen := SectionRetainedProjOpens.toProj_preimage_basicOpen L q h (s i) hd
    have hyi : y ∈ chart s i := by
      change x ∈ sectionGeneratorOpen (tensorPower L (q * d)) (s i) at hxi
      change y ∈ sectionGeneratorOpen (tensorPower L (q * d)) (s i)
      rw [← hopen] at hxi ⊢
      change toProj L q h y ∈
        Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q) (insertion L q d (s i))
      rw [← hxy]
      exact hxi
    have he : ((chart s i).ι ≫ toProj L q h) ⟨x, hxi⟩ =
        ((chart s i).ι ≫ toProj L q h) ⟨y, hyi⟩ := hxy
    exact congrArg Subtype.val ((hi i).base_open.injective he)
  apply IsOpenImmersion.of_openCover_source (toProj L q h)
    (X.openCoverOfIsOpenCover (chart s) hcover) hinj
  exact hi

end FLT.Mazur.SectionRetainedProjOfAmple
