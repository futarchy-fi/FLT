/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteProjectiveTildeLocal

/-!
# Prescribed local frame types and geometric descent

Transport a finite frame on a subopen of a chart to its image in the base.
This constructs finite free neighborhoods for the original global sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ModuleSheafLocalFrames
universe u v
variable {X : Scheme.{u}} (τ : Type u) (M : X.Modules)

/-- Local frames with one prescribed index type on every neighborhood. -/
def HasFrames : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (M.restrict U.ι ≅ SheafOfModules.free τ)

/-- An actual sheaf isomorphism preserves the specified frame type. -/
theorem HasFrames.of_iso {M N : X.Modules} (hM : HasFrames τ M) (e : M ≅ N) :
    HasFrames τ N := by
  intro x
  obtain ⟨U, hx, ⟨t⟩⟩ := hM x
  exact ⟨U, hx, ⟨((restrictFunctor U.ι).mapIso e).symm ≪≫ t⟩⟩

/-- Arbitrary scheme pullback preserves the specified local frame type. -/
theorem HasFrames.pullback {Y : Scheme.{u}} (hM : HasFrames τ M) (f : Y ⟶ X) :
    HasFrames τ ((Scheme.Modules.pullback f).obj M) := by
  intro x
  obtain ⟨U, hx, ⟨t⟩⟩ := hM (f x)
  exact ⟨f ⁻¹ᵁ U, hx, ⟨FCurve.modulePullbackOpenIso f U M ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso t ≪≫
      ModuleGlobalEvaluationPullback.freeIso (f ∣_ U) τ⟩⟩

/-- Fixed-type frames descend from a covering family of actual open subschemes. -/
theorem HasFrames.of_openCover {ι : Type v} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (hM : ∀ i, HasFrames τ ((Scheme.Modules.pullback (U i).ι).obj M)) :
    HasFrames τ M := by
  intro x
  obtain ⟨i, hx⟩ := Opens.mem_iSup.mp (show x ∈ iSup U by rw [hU]; trivial)
  have hr := (hM i).of_iso τ ((restrictFunctorIsoPullback (U i).ι).app M).symm
  obtain ⟨V, hv, ⟨e⟩⟩ := hr ⟨x, hx⟩
  let j := V.ι ≫ (U i).ι
  let a := (restrictFunctorComp V.ι (U i).ι).app M ≪≫ e
  let b := (restrictFunctorComp j.isoOpensRange.inv j).symm ≪≫
    restrictFunctorCongr j.isoOpensRange_inv_comp
  refine ⟨j.opensRange, ⟨⟨⟨x, hx⟩, hv⟩, rfl⟩, ⟨?_⟩⟩
  exact (b.app M).symm ≪≫ (restrictFunctor j.isoOpensRange.inv).mapIso a ≪≫
    (restrictFunctorIsoPullback j.isoOpensRange.inv).app _ ≪≫
      ModuleGlobalEvaluationPullback.freeIso j.isoOpensRange.inv τ

end FLT.Mazur.ModuleSheafLocalFrames
