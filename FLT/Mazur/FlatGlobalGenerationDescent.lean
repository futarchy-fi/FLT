/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffinePullbackEpiReflection
public import FLT.Mazur.FlatGlobalSectionExpansion
public import FLT.Mazur.GlobalEvaluationSpan

/-!
# Descent of global generation under affine faithfully flat base change

Finite expansions show that the pulled-back downstairs sections span all
upstairs sections. Reflection of the actual evaluation epimorphism then
descends global generation, with no reducedness or Noetherian assumptions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.FlatGlobalGenerationDescent
open FCurve ProjectiveSpace OpenModuleSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S} [Flat g]
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h

/-- The pulled-back global sections span all global sections over the upstairs ring. -/
theorem span_pullGlobal :
    Submodule.span Γ(P, ⊤) (Set.range (pullGlobal p M)) = ⊤ := by
  apply top_unique
  intro s _
  obtain ⟨t, ht⟩ := FlatGlobalSectionExpansion.exists_sum_pullGlobal h M
    (show openSections q ((pullback p).obj M) ⊤ from s)
  change s = ∑ a ∈ t, _ at ht
  rw [ht]
  apply Submodule.sum_mem
  intro a ha
  change P.presheaf.map (homOfLE (show (⊤ : P.Opens) ≤ ⊤ from le_top)).op
    (q.appTop a.1) • pullGlobal p M a.2 ∈ _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a.2, rfl⟩)

/-- Generation upstairs is already generation by the pulled-back downstairs sections. -/
theorem pulled_family_epi
    [Epi (globalEvaluation ((pullback p).obj M) (fun s : Γ((pullback p).obj M, ⊤) ↦ s))] :
    Epi (globalEvaluation ((pullback p).obj M) (pullGlobal p M)) :=
  GlobalEvaluationSpan.epi_of_span _ (span_pullGlobal h M)

/-- Global generation descends from an affine faithfully flat base change. -/
theorem globalEvaluation_epi [Surjective g]
    [Epi (globalEvaluation ((pullback p).obj M) (fun s : Γ((pullback p).obj M, ⊤) ↦ s))] :
    Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s)) := by
  have : IsAffineHom p := MorphismProperty.of_isPullback h.flip (inferInstance : IsAffineHom g)
  have : Flat p := MorphismProperty.of_isPullback h.flip (inferInstance : Flat g)
  have : Surjective p := MorphismProperty.of_isPullback h.flip (inferInstance : Surjective g)
  have := GlobalEvaluationSpan.free_isQuasicoherent (X := X) Γ(M, ⊤)
  have := pulled_family_epi h M
  have : Epi ((pullback p).map (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s))) := by
    rw [ModuleGlobalEvaluationPullback.evaluation_pullback]
    infer_instance
  exact AffinePullbackEpiReflection.epi_of_pullback p _

/-- Global generation is equivalent before and after affine faithfully flat base change. -/
theorem globalEvaluation_epi_iff [Surjective g] :
    Epi (globalEvaluation ((pullback p).obj M) (fun s : Γ((pullback p).obj M, ⊤) ↦ s)) ↔
      Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s)) := by
  constructor
  · intro he
    exact globalEvaluation_epi h M
  · intro he
    have := ModuleGlobalEvaluationPullback.evaluation_epi p M (fun s : Γ(M, ⊤) ↦ s)
    exact GlobalEvaluationSpan.all_epi_of_epi (pullGlobal p M)

end FLT.Mazur.FlatGlobalGenerationDescent
