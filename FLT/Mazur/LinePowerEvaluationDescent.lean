/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleGlobalGeneration
public import FLT.Mazur.FpqcGlobalGenerationDescent
public import FLT.Mazur.PrincipalSectionExtension

/-!
# Descent of generation in each line-bundle degree

Tensor-power pullback coherence identifies the actual evaluation consumers.
An ample fpqc pullback gives a globally generated positive power downstairs;
this result makes no ampleness conclusion downstairs.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.LinePowerEvaluationDescent
open FCurve ProjectiveSpace ModuleLineBundleTensorPullback GlobalGenerationTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}} [CompactSpace X] [X.IsSeparated] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [Flat g] [Surjective g] [QuasiCompact g]
  (h : IsPullback p q f g) {L : X.Modules} (hL : LocallyFreeRankOne L)

include h hL in
/-- Fpqc base change reflects and preserves global generation in each tensor degree. -/
theorem degree_evaluation_epi_iff (n : ℕ) :
    Epi (globalEvaluation (tensorPower ((pullback p).obj L) n)
      (fun s : Γ(tensorPower ((pullback p).obj L) n, ⊤) ↦ s)) ↔
    Epi (globalEvaluation (tensorPower L n) (fun s : Γ(tensorPower L n, ⊤) ↦ s)) := by
  have := (hL.tensorPower n).isFinitePresentation
  let e := tensorPowerIso p L n
  constructor
  · intro he
    have := all_epi_of_iso e.symm
    exact FpqcGlobalGenerationDescent.globalEvaluation_epi h (tensorPower L n)
  · intro he
    have := all_epi_pullback p (tensorPower L n)
    exact all_epi_of_iso e

include h hL in
/-- Existence of a globally generated positive degree is fpqc invariant. -/
theorem exists_positive_evaluation_iff :
    (∃ n : ℕ, 0 < n ∧ Epi (globalEvaluation (tensorPower ((pullback p).obj L) n)
      (fun s : Γ(tensorPower ((pullback p).obj L) n, ⊤) ↦ s))) ↔
    ∃ n : ℕ, 0 < n ∧ Epi (globalEvaluation (tensorPower L n)
      (fun s : Γ(tensorPower L n, ⊤) ↦ s)) := by
  simp only [degree_evaluation_epi_iff h hL]

include h hL in
/-- An ample fpqc pullback supplies an actual generated positive power downstairs. -/
theorem exists_positive_evaluation_of_ample
    (hA : AmpleLineBundle ((pullback p).obj L)) :
    ∃ n : ℕ, 0 < n ∧ Epi (globalEvaluation (tensorPower L n)
      (fun s : Γ(tensorPower L n, ⊤) ↦ s)) :=
  (exists_positive_evaluation_iff h hL).mp hA.exists_positive_globalEvaluation

end FLT.Mazur.LinePowerEvaluationDescent
