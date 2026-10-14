/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleSectionChartCover
public import FLT.Mazur.SectionGradedProjOfAmple
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Recovering a proper scheme from its full tensor-graded sections

For an ample line on a scheme proper over a noetherian affine base, the
original affine generator charts cover the whole full Proj. The canonical
open immersion is consequently surjective and is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.ProperAmpleSectionProjIso

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover
open SectionGradedChartComparison SectionGradedChartMorphism
open SectionGradedProjConstruction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules) [Fact (LocallyFreeRankOne L)]

include f

/-- Every point of the full Proj comes from the original proper scheme. -/
theorem surjective (hA : AmpleLineBundle L) (h : PositivePowerGenerated L) :
    Function.Surjective (toProj L h) := by
  obtain ⟨I, hI, a, ha, s, haff, hcover, hproj⟩ :=
    ProperAmpleSectionChartCover.exists_cover f L hA
  let _ := hI
  intro z
  have hz : z ∈ ⨆ i, Proj.basicOpen (grade L ⊤)
      (of L ⊤ a (s i)) := by rw [hproj]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  rw [← Proj.opensRange_awayι _ _ (show of L ⊤ a (s i) ∈ grade L ⊤ a from ⟨s i, rfl⟩) ha] at hi
  obtain ⟨w, hw⟩ := hi
  let g := (chart s i).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (toFunctions L a (s i) (chart s i) le_rfl))
  have : IsIso (CommRingCat.ofHom (toFunctions L a (s i) (chart s i) le_rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨SectionGradedChartIsomorphism.injective L a s haff hcover i,
        SectionGradedChartIsomorphism.surjective L a s haff hcover i⟩
  have : IsIso (chart s i).toSpecΓ := by
    rw [← (haff i).isoSpec_hom]
    infer_instance
  have : IsIso g := by dsimp only [g]; infer_instance
  obtain ⟨x, hx⟩ := g.surjective w
  refine ⟨(chart s i).ι x, ?_⟩
  have he := congrArg (fun k ↦ k x) (toProjOn_eq L a (s i) ha h (chart s i) le_rfl)
  change (g ≫ Proj.awayι _ _ (show of L ⊤ a (s i) ∈ grade L ⊤ a from ⟨s i, rfl⟩) ha) x = _ at he
  rw [Scheme.Hom.comp_apply, hx, hw] at he
  exact he.symm

/-- The original proper scheme is its original full section-ring Proj. -/
theorem isIso (hA : AmpleLineBundle L) (h : PositivePowerGenerated L) :
    IsIso (toProj L h) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨SectionGradedProjOfAmple.isOpenImmersion L hA h, ⟨surjective f L hA h⟩⟩

/-- The recovery isomorphism retains the actual canonical section-evaluation morphism. -/
def iso (hA : AmpleLineBundle L) (h : PositivePowerGenerated L) :
    X ≅ Proj (grade L ⊤) := by
  let _ := isIso f L hA h
  exact asIso (toProj L h)

/-- Recovery has the original canonical morphism as its forward map. -/
theorem iso_hom (hA : AmpleLineBundle L) (h : PositivePowerGenerated L) :
    (iso f L hA h).hom = toProj L h := rfl

end FLT.Mazur.ProperAmpleSectionProjIso
