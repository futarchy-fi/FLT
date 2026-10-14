/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleRetainedChartGeneration
public import FLT.Mazur.GradedProjEventualGenerationCover

/-!
# Affine section charts cover the full section-ring Proj

Proper coherent vanishing makes an actual affine generator family generate
all high degrees. Its basic opens cover the full tensor-graded Proj.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.ProperAmpleSectionChartCover
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules) [Fact (LocallyFreeRankOne L)]

include f

/-- The same actual sections cover both the proper scheme and its entire section-ring Proj. -/
theorem exists_cover (hA : AmpleLineBundle L) :
    ∃ (I : Type) (_ : Fintype I) (a : ℕ) (_ : 0 < a)
      (s : I → Γ(tensorPower L a, ⊤)),
      (∀ i, IsAffineOpen (chart s i)) ∧ (⨆ i, chart s i = ⊤) ∧
      ⨆ i, Proj.basicOpen (grade L ⊤) (of L ⊤ a (s i)) = ⊤ := by
  classical
  obtain ⟨I, hI, a, ha, s, haff, hcover⟩ := hA.common_degree_section_cover
  let _ := hI
  let _ := Fintype.ofFinite I
  have hs : Epi (ProjectiveSpace.globalEvaluation (tensorPower L a) s) :=
    globalEvaluation_epi_of_sectionHom_isIso s (chart s) hcover id
      (fun j ↦ sectionHom_generatorOpen_isIso (tensorPower L a) (s j))
  let _ := (hA.2.1.tensorPower a).isFinitePresentation
  obtain ⟨B, hB⟩ := ample_twisted_sections_surjective f hA
    (ProjectiveSpace.globalEvaluation (tensorPower L a) s)
  refine ⟨I, inferInstance, a, ha, s, haff, hcover, ?_⟩
  apply GradedProjEventualGenerationCover.iSup_basicOpen_eq_top _ _ (a + B)
  intro d hd z hz
  obtain ⟨b, rfl⟩ : ∃ b, d = a + b := ⟨d - a, by omega⟩
  obtain ⟨v, rfl⟩ := hz
  obtain ⟨t, ht⟩ := section_mul_sum_of_twistedEvaluation_surjective L a b
    s (hB b (by omega)) v
  rw [ht, map_sum]
  simp_rw [← mul_of]
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self j))

end FLT.Mazur.ProperAmpleSectionChartCover
