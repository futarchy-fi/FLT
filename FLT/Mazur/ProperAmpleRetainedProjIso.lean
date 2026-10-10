/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleRetainedChartCover
public import FLT.Mazur.SectionRetainedProjOfAmple
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Recovering a proper scheme from its original retained sections

For an ample line on a scheme proper over a noetherian affine base, the
original affine generator charts cover the whole retained Proj. The canonical
open immersion is consequently surjective and is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.ProperAmpleRetainedProjIso

open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionCover
open SectionRetainedChartComparison SectionRetainedChartMorphism
open SectionRetainedProjConstruction

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] (L : X.Modules) [Fact (LocallyFreeRankOne L)]
  (q : ℕ) [GradedRing (RetainedSubringGrading.grade (grade L ⊤) q)]

include f

/-- Every point of the retained Proj comes from the original proper scheme. -/
theorem surjective (hA : AmpleLineBundle L) (hq : 0 < q) (h : PositivePowerGenerated L q) :
    Function.Surjective (toProj L q h) := by
  obtain ⟨I, hI, a, ha, s, haff, hcover, hproj⟩ :=
    ProperAmpleRetainedChartCover.exists_cover f L q hA hq
  let _ := hI
  intro z
  have hz : z ∈ ⨆ i, Proj.basicOpen (RetainedSubringGrading.grade (grade L ⊤) q)
      (insertion L q a (s i)) := by rw [hproj]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
  rw [← Proj.opensRange_awayι _ _ (insertion_mem L q a (s i)) ha] at hi
  obtain ⟨w, hw⟩ := hi
  let g := (chart s i).toSpecΓ ≫
    Spec.map (CommRingCat.ofHom (toFunctions L q a (s i) (chart s i) le_rfl))
  have : IsIso (CommRingCat.ofHom (toFunctions L q a (s i) (chart s i) le_rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (ringEquiv L q a s haff hcover i).bijective
  have : IsIso (chart s i).toSpecΓ := by
    rw [← (haff i).isoSpec_hom]
    infer_instance
  have : IsIso g := by dsimp only [g]; infer_instance
  obtain ⟨x, hx⟩ := g.surjective w
  refine ⟨(chart s i).ι x, ?_⟩
  have he := congrArg (fun k ↦ k x) (toProjOn_eq L q a (s i) ha h (chart s i) le_rfl)
  change (g ≫ Proj.awayι _ _ (insertion_mem L q a (s i)) ha) x = _ at he
  rw [Scheme.Hom.comp_apply, hx, hw] at he
  exact he.symm

/-- The original proper scheme is its original positively retained section-ring Proj. -/
theorem isIso (hA : AmpleLineBundle L) (hq : 0 < q) (h : PositivePowerGenerated L q) :
    IsIso (toProj L q h) :=
  (isIso_iff_isOpenImmersion_and_surjective _).mpr
    ⟨SectionRetainedProjOfAmple.isOpenImmersion L q hq hA h, ⟨surjective f L q hA hq h⟩⟩

/-- The recovery isomorphism retains the actual canonical section-evaluation morphism. -/
def iso (hA : AmpleLineBundle L) (hq : 0 < q) (h : PositivePowerGenerated L q) :
    X ≅ Proj (RetainedSubringGrading.grade (grade L ⊤) q) := by
  let _ := isIso f L q hA hq h
  exact asIso (toProj L q h)

/-- Recovery has the original canonical morphism as its forward map. -/
theorem iso_hom (hA : AmpleLineBundle L) (hq : 0 < q) (h : PositivePowerGenerated L q) :
    (iso f L q hA hq h).hom = toProj L q h := rfl

end FLT.Mazur.ProperAmpleRetainedProjIso
