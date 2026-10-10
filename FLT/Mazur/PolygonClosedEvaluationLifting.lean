/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleTwistedSectionLifting
public import FLT.Mazur.AmpleGlobalGeneration
public import FLT.Mazur.CoherentFreeSheaf
public import FLT.Mazur.PolygonInfinitesimalStageAmple
public import FLT.Mazur.PolygonInfinitesimalStageProper

/-!
# A fixed finite evaluation generating all sufficiently positive closed twists

Choose a finite generating family in a positive power of the original
closed-stage boundary line. Its original evaluation, tensored by higher
powers, lifts every section with one bound independent of the exponent.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.PolygonInfinitesimalStages

open FCurve ModuleLineBundleTensorPullback ProjectiveSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] boundaryLine family

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n)

/-- One finite family has surjective original evaluation in every sufficiently positive twist. -/
theorem boundaryClosedEvaluation_eventually_surjective :
    ∃ a : ℕ, 0 < a ∧ ∃ (κ : Type) (_ : Finite κ)
      (s : κ → Γ(tensorPower (boundaryLine K 0 n h) a, ⊤)),
      Epi (globalEvaluation (tensorPower (boundaryLine K 0 n h) a) s) ∧
      ∃ B : ℕ, ∀ d ≥ B, Function.Surjective
        ((ModuleSheafTensor.map
          (globalEvaluation (tensorPower (boundaryLine K 0 n h) a) s)
          (𝟙 (tensorPower (boundaryLine K 0 n h) d))).app ⊤) := by
  obtain ⟨a, ha, κ, hκ, s, hs⟩ :=
    (boundaryLine_ample K 0 n h).exists_positive_finite_evaluation
  let _ := hκ
  let _ := hs
  let _ := ((boundaryLine_rankOne K 0 n h).tensorPower a).isFinitePresentation
  exact ⟨a, ha, κ, hκ, s, hs, ample_twisted_sections_surjective
    (family K 0 n h).hom (boundaryLine_ample K 0 n h)
      (globalEvaluation (tensorPower (boundaryLine K 0 n h) a) s)⟩

/-- The same evaluation reaches the original additive tensor degree through its specified iso. -/
theorem boundaryClosedEvaluation_add_surjective {a d : ℕ} {κ : Type}
    (s : κ → Γ(tensorPower (boundaryLine K 0 n h) a, ⊤))
    (hs : Function.Surjective ((ModuleSheafTensor.map
      (globalEvaluation (tensorPower (boundaryLine K 0 n h) a) s)
      (𝟙 (tensorPower (boundaryLine K 0 n h) d))).app ⊤)) :
    Function.Surjective (fun u ↦
      (tensorPowerAddIso (boundaryLine K 0 n h) a d).hom.app ⊤
        ((ModuleSheafTensor.map
          (globalEvaluation (tensorPower (boundaryLine K 0 n h) a) s)
          (𝟙 (tensorPower (boundaryLine K 0 n h) d))).app ⊤ u)) :=
  (ConcreteCategory.bijective_of_isIso
    ((tensorPowerAddIso (boundaryLine K 0 n h) a d).hom.app ⊤)).2.comp hs

end FLT.Mazur.PolygonInfinitesimalStages
