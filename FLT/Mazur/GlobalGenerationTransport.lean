/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GlobalEvaluationSpan

/-!
# Transport of global generation

Global generation, expressed by the actual evaluation morphism, survives
module isomorphisms and pullback along arbitrary scheme morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.GlobalGenerationTransport
open ProjectiveSpace GlobalEvaluationSpan
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}}

/-- Global generation is transported through a module isomorphism. -/
theorem all_epi_of_iso {M N : X.Modules} (e : M ≅ N)
    [Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s))] :
    Epi (globalEvaluation N (fun s : Γ(N, ⊤) ↦ s)) where
  left_cancellation a b h := by
    apply (cancel_epi e.hom).mp
    apply (cancel_epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s))).mp
    apply evaluation_comp_eq
    intro m
    have he := globalEvaluation_cancel (fun s : Γ(N, ⊤) ↦ s) a b h (e.hom.app ⊤ m) ⊤
    simpa using he

/-- Arbitrary scheme pullback preserves global generation. -/
theorem all_epi_pullback (f : X ⟶ Y) (M : Y.Modules)
    [Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s))] :
    Epi (globalEvaluation ((pullback f).obj M) (fun s : Γ((pullback f).obj M, ⊤) ↦ s)) := by
  have := ModuleGlobalEvaluationPullback.evaluation_epi f M (fun s : Γ(M, ⊤) ↦ s)
  exact all_epi_of_epi (FCurve.pullGlobal f M)

end FLT.Mazur.GlobalGenerationTransport
