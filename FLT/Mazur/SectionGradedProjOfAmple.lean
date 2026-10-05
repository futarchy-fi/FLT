/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedChartMorphism
public import FLT.Mazur.SectionGradedChartIsomorphism
public import FLT.Mazur.SectionGradedProjAmpleOfOpenImmersion

/-!
# Ampleness and the canonical section-ring Proj map

A finite affine generator cover identifies its homogeneous localizations
with its rings of functions. Thus the canonical map is an open immersion
on each chart. Its exact generator-open inverse images give global
injectivity, proving the forward ampleness criterion.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedProjOfAmple
open FCurve ModuleLineBundleTensorPullback SectionCover SectionGradedSum
open SectionGradedProjConstruction SectionGradedChartComparison SectionGradedChartMorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme} (L : X.Modules) [Fact (LocallyFreeRankOne L)]

/-- The canonical map is an open immersion on each chart of a finite affine generator cover. -/
lemma chart_isOpenImmersion (h : PositivePowerGenerated L) {ι : Type*} [Finite ι]
    (d : ℕ) (s : ι → Γ(tensorPower L d, ⊤)) (hd : 0 < d)
    (haff : ∀ j, IsAffineOpen (chart s j)) (hcover : ⨆ j, chart s j = ⊤) (i : ι) :
    IsOpenImmersion ((chart s i).ι ≫ toProj L h) := by
  rw [← toProjOn_eq L d (s i) hd h (chart s i) le_rfl]
  have : IsIso (CommRingCat.ofHom (toFunctions L d (s i) (chart s i) le_rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨SectionGradedChartIsomorphism.injective L d s haff hcover i,
        SectionGradedChartIsomorphism.surjective L d s haff hcover i⟩
  have : IsIso (chart s i).toSpecΓ := by
    rw [← (haff i).isoSpec_hom]
    infer_instance
  unfold toProjOn
  infer_instance

/-- Ampleness implies that the actual canonical section-ring Proj map is an open immersion. -/
theorem isOpenImmersion (hA : AmpleLineBundle L) (h : PositivePowerGenerated L) :
    IsOpenImmersion (toProj L h) := by
  obtain ⟨ι, hι, d, hd, s, haff, hcover⟩ := hA.common_degree_section_cover
  let := hι
  have hi (i : ι) := chart_isOpenImmersion L h d s hd haff hcover i
  have hinj : Function.Injective (toProj L h) := by
    intro x y hxy
    have hx : x ∈ ⨆ i, chart s i := by rw [hcover]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    have hopen := SectionGradedProjOpens.toProj_preimage_basicOpen L h (s i) hd
    have hyi : y ∈ chart s i := by
      change x ∈ sectionGeneratorOpen (tensorPower L d) (s i) at hxi
      change y ∈ sectionGeneratorOpen (tensorPower L d) (s i)
      rw [← hopen] at hxi ⊢
      change toProj L h y ∈ Proj.basicOpen (grade L ⊤) (of L ⊤ d (s i))
      rw [← hxy]
      exact hxi
    have he : ((chart s i).ι ≫ toProj L h) ⟨x, hxi⟩ =
        ((chart s i).ι ≫ toProj L h) ⟨y, hyi⟩ := hxy
    exact congrArg Subtype.val ((hi i).base_open.injective he)
  apply IsOpenImmersion.of_openCover_source (toProj L h)
    (X.openCoverOfIsOpenCover (chart s) hcover) hinj
  exact hi

/-- On a compact line bundle, ampleness is equivalent to the canonical open-immersion criterion. -/
theorem ample_iff [CompactSpace X] (h : PositivePowerGenerated L) :
    AmpleLineBundle L ↔ IsOpenImmersion (toProj L h) := by
  constructor
  · intro hA
    exact isOpenImmersion L hA h
  · intro hi
    exact SectionGradedProjAmpleOfOpenImmersion.ample L h

end FLT.Mazur.SectionGradedProjOfAmple
