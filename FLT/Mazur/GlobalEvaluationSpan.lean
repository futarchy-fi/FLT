/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleGlobalEvaluationPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Global evaluation and spanning families

A family spanning all global sections generates whenever the full global
section family generates. Free source sheaves are quasi-coherent for arbitrary
index types, with no finiteness assumption.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
universe u
namespace FLT.Mazur.GlobalEvaluationSpan
open ProjectiveSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}}

/-- Free module sheaves are quasi-coherent, including infinite rank. -/
lemma free_isQuasicoherent (κ : Type u) :
    (SheafOfModules.free (R := X.ringCatSheaf) κ).IsQuasicoherent :=
  ((SheafOfModules.free.generatingSections (R := X.ringCatSheaf) κ).localGeneratorsData)
    |>.quasiCoherentData.isQuasicoherent

/-- Equality after evaluation is detected on the given global sections. -/
lemma evaluation_comp_eq {M N : X.Modules} {κ : Type u} (s : κ → Γ(M, ⊤))
    (a b : M ⟶ N) (h : ∀ i, a.app ⊤ (s i) = b.app ⊤ (s i)) :
    globalEvaluation M s ≫ a = globalEvaluation M s ≫ b := by
  apply N.freeHomEquiv.injective
  funext i
  rw [SheafOfModules.freeHomEquiv_comp_apply,
    SheafOfModules.freeHomEquiv_comp_apply]
  simp only [globalEvaluation, Equiv.apply_symm_apply]
  apply Subtype.ext
  funext U
  change a.val.app U (M.val.map (homOfLE le_top).op (s i)) =
    b.val.app U (M.val.map (homOfLE le_top).op (s i))
  rw [PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply]
  exact congrArg (N.val.map (homOfLE le_top).op) (h i)

/-- A spanning family has epimorphic evaluation if all global sections do. -/
theorem epi_of_span {M : X.Modules} {κ : Type u} (s : κ → Γ(M, ⊤))
    (hs : Submodule.span Γ(X, ⊤) (Set.range s) = ⊤)
    [Epi (globalEvaluation M (fun t : Γ(M, ⊤) ↦ t))] :
    Epi (globalEvaluation M s) where
  left_cancellation a b h := by
    apply (cancel_epi (globalEvaluation M (fun t : Γ(M, ⊤) ↦ t))).mp
    apply evaluation_comp_eq
    intro t
    have ht : t ∈ Submodule.span Γ(X, ⊤) (Set.range s) := by rw [hs]; trivial
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨i, rfl⟩ := ht
      have he := globalEvaluation_cancel s a b h i ⊤
      simpa using he
    | zero => simp only [map_zero]
    | add x y hx hy hax hay => simp only [map_add, hax, hay]
    | smul r x hx hax => simp only [Hom.app_smul, hax]

/-- Epimorphic evaluation of any family implies generation by all global sections. -/
theorem all_epi_of_epi {M : X.Modules} {κ : Type u} (s : κ → Γ(M, ⊤))
    [Epi (globalEvaluation M s)] : Epi (globalEvaluation M (fun t : Γ(M, ⊤) ↦ t)) where
  left_cancellation a b h := by
    apply (cancel_epi (globalEvaluation M s)).mp
    apply evaluation_comp_eq
    intro i
    have he := globalEvaluation_cancel (fun t : Γ(M, ⊤) ↦ t) a b h (s i) ⊤
    simpa using he

end FLT.Mazur.GlobalEvaluationSpan
