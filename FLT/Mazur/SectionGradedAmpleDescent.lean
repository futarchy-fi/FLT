/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedProjOfAmple
public import FLT.Mazur.SectionGradedProjFpqcDescent
public import FLT.Mazur.SectionGeneratorSpan
public import FLT.Mazur.FlatGlobalGenerationDescent
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Ampleness descends along affine faithfully flat base change

Flat base change expands every upstairs section in the span of actual
pulled-back downstairs sections. Generator opens of linear combinations
supply positive-power generation downstairs. The canonical Proj criterion
and its Cartesian square then descend ampleness without assuming generation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SectionGradedAmpleDescent
open FCurve ModuleLineBundleTensorPullback SectionGradedProjConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g] [Surjective g]
  (h : IsPullback p q f g) (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]

include h in
/-- An ample faithfully flat pullback supplies generating positive-power sections downstairs. -/
lemma positivePowerGenerated (hA : AmpleLineBundle ((pullback p).obj L)) :
    PositivePowerGenerated L := by
  have : Surjective p := MorphismProperty.of_isPullback h.flip (inferInstance : Surjective g)
  intro x
  obtain ⟨y, rfl⟩ := p.surjective x
  obtain ⟨n, hn, t, hyt, _⟩ := hA.2.2 y
  let e := tensorPowerIso p L n
  let t' := e.inv.app ⊤ t
  have hy : y ∈ sectionGeneratorOpen ((pullback p).obj (tensorPower L n)) t' := by
    rw [show sectionGeneratorOpen ((pullback p).obj (tensorPower L n)) t' =
      sectionGeneratorOpen (tensorPower ((pullback p).obj L) n) t from
        sectionGeneratorOpen_iso e.symm t]
    exact hyt
  have := (hL.out.tensorPower n).isFinitePresentation
  have ht' : t' ∈ Submodule.span Γ(P, ⊤) (Set.range (pullGlobal p (tensorPower L n))) := by
    rw [FlatGlobalGenerationDescent.span_pullGlobal h (tensorPower L n)]
    trivial
  have hu := sectionGeneratorOpen_le_of_mem_span ((pullback p).obj (tensorPower L n))
    (pullGlobal p (tensorPower L n)) ht'
  obtain ⟨s, hs⟩ := TopologicalSpace.Opens.mem_iSup.mp (hu hy)
  refine ⟨n, hn, s, ?_⟩
  rw [sectionGeneratorOpen_pullGlobal (hL.out.tensorPower n) p s] at hs
  exact hs

include h in
/-- Ampleness of the actual line bundle descends along an affine faithfully flat base change. -/
theorem ample_of_pullback (hA : AmpleLineBundle ((pullback p).obj L)) : AmpleLineBundle L := by
  let hg := positivePowerGenerated h L hA
  let : Fact (LocallyFreeRankOne ((pullback p).obj L)) := ⟨hL.out.pullback p⟩
  have hu := SectionGradedProjOfAmple.isOpenImmersion ((pullback p).obj L) hA
    (SectionGradedProjNaturality.positivePowerGenerated_pullback p L hg)
  have : IsOpenImmersion (toProj L hg) :=
    (SectionGradedProjFpqcDescent.isOpenImmersion_iff h L hg).mp hu
  exact SectionGradedProjAmpleOfOpenImmersion.ample L hg

include h in
/-- Section-open ampleness is invariant under affine faithfully flat base change. -/
theorem ample_iff : AmpleLineBundle ((pullback p).obj L) ↔ AmpleLineBundle L := by
  refine ⟨ample_of_pullback h L, fun hA ↦ ?_⟩
  have : IsAffineHom p := MorphismProperty.of_isPullback h.flip (inferInstance : IsAffineHom g)
  exact hA.pullback_affine p

end FLT.Mazur.SectionGradedAmpleDescent
