/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveTildeLocal

/-!
# Finite free sheaf charts descend through open covers

Transport a finite frame on a subopen of a chart to its image in the base.
This constructs finite free neighborhoods for the original global sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve
universe u v
variable {X : Scheme.{u}} (M : X.Modules)

/-- Finite local freeness descends from geometric pullbacks to a covering family. -/
lemma locallyFiniteFree_of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (hM : ∀ i, LocallyFiniteFree ((pullback (U i).ι).obj M)) :
    LocallyFiniteFree M := by
  intro x
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
  have hr := (hM i).of_iso ((restrictFunctorIsoPullback (U i).ι).app M).symm
  obtain ⟨V, hv, κ, hκ, ⟨e⟩⟩ := hr ⟨x, hx⟩
  let j := V.ι ≫ (U i).ι
  let a := (restrictFunctorComp V.ι (U i).ι).app M ≪≫ e
  let b := (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  refine ⟨j.opensRange, ⟨⟨⟨x, hx⟩, hv⟩, rfl⟩, κ, hκ, ⟨?_⟩⟩
  exact (b.app M).symm ≪≫ (restrictFunctor j.isoOpensRange.inv).mapIso a ≪≫
    (restrictFunctorIsoPullback j.isoOpensRange.inv).app _ ≪≫
      ModuleGlobalEvaluationPullback.freeIso j.isoOpensRange.inv κ
end FLT.Mazur.FCurve
