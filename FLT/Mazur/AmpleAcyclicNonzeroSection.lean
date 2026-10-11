/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCoherentVanishing
public import FLT.Mazur.AmpleHighDegreeSectionCover
public import FLT.Mazur.SectionGeneratorSpan
public import FLT.Mazur.PrincipalSectionExtension

/-!
# An acyclic ample power with an actual nonzero section

Choose a section cover in a degree above the proper Serre-vanishing bound.
On a nonempty scheme at least one of those original sections is nonzero.
No integral, smooth, or constant-global-functions hypothesis is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback

variable {k : Type} [Field k] {X : Scheme} [Nonempty X]
  (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Some acyclic power of the original ample line has a nonzero global section. -/
theorem exists_acyclic_power_nonzero_section {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ n : ℕ, 0 < n ∧ Subsingleton (ModuleScalarH f (tensorPower B n) 1) ∧
      ∃ s : Γ(tensorPower B n, ⊤), s ≠ 0 := by
  let _ := structureModule_locallyFreeRankOne.isFinitePresentation (X := X)
  obtain ⟨N, hN⟩ := hB.coherent_vanishing f (structureModule X)
  obtain ⟨n, hn, hp, ι, _, s, _, hcover⟩ := hB.high_degree_section_cover N
  let x : X := Classical.choice inferInstance
  have hx : x ∈ ⨆ i, sectionGeneratorOpen (tensorPower B n) (s i) := hcover ▸ trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hv := hN n hn 0
  have hz : Subsingleton (ModuleH (tensorPower B n) 1) :=
    @moduleH_subsingleton_of_iso X _ _ (leftUnitor (tensorPower B n)).symm 1 hv
  refine ⟨n, hp, hz, s i, ?_⟩
  intro hs
  rw [hs, sectionGeneratorOpen_zero] at hi
  exact hi

/-- A proper nonempty ample scheme has an acyclic line with a nonzero section. -/
theorem exists_acyclic_line_nonzero_section {B : X.Modules} (hB : AmpleLineBundle B) :
    ∃ L : X.Modules, LocallyFreeRankOne L ∧ Subsingleton (ModuleScalarH f L 1) ∧
      ∃ s : Γ(L, ⊤), s ≠ 0 := by
  obtain ⟨n, _, hz, s, hs⟩ := exists_acyclic_power_nonzero_section f hB
  exact ⟨tensorPower B n, hB.2.1.tensorPower n, hz, s, hs⟩

end FLT.Mazur.FCurve
