/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjCoefficientSections
public import FLT.Mazur.ModuleGlobalEvaluationPullback

/-!
# The original coefficient coordinates generate the complete line

Each constructed global coordinate is the unit on its own chart. The actual
global evaluation is therefore epimorphic, also after any scheme pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.GradedProjLine

open FCurve

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {ι : Type} (f : ι → A)
  {d : ℕ} (hf : ∀ i, f i ∈ 𝒜 d)

/-- The original coordinate section trivializes the coefficient line on its own chart. -/
theorem coefficientSection_isIso (i : ι) :
    IsIso (sectionHom (line 𝒜 f hf 1) (chart 𝒜 f i)
      ((line 𝒜 f hf 1).presheaf.map (homOfLE le_top).op
        (coefficientSection 𝒜 f hf i))) := by
  let g := cocycle 𝒜 f hf 1
  let e : Γ(line 𝒜 f hf 1, chart 𝒜 f i) ≃ₗ[Γ(Proj 𝒜, chart 𝒜 f i)]
      Γ(Proj 𝒜, chart 𝒜 f i) :=
    { g.evaluationEquiv i le_rfl with map_smul' := g.evaluate_smul i le_rfl }
  apply sectionHom_isIso_of_linear_coordinate _ _ (g.restrictIso i) e
  change IsUnit ((cocycle 𝒜 f hf 1).evaluate i le_rfl _)
  rw [coefficientSection_evaluate_self]
  exact isUnit_one

/-- A covering coordinate family gives an epimorphism from the original free module. -/
theorem coefficientSection_evaluation_epi (hcover : (⨆ i, chart 𝒜 f i) = ⊤) :
    Epi (ProjectiveSpace.globalEvaluation (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf)) :=
  globalEvaluation_epi_of_sectionHom_isIso (coefficientSection 𝒜 f hf)
    (chart 𝒜 f) hcover id (coefficientSection_isIso 𝒜 f hf)

/-- Pullbacks of these same global coordinates generate the actual pulled-back line. -/
theorem coefficientSection_pullback_evaluation_epi
    (hcover : (⨆ i, chart 𝒜 f i) = ⊤) {X : Scheme} (p : X ⟶ Proj 𝒜) :
    Epi (ProjectiveSpace.globalEvaluation ((pullback p).obj (line 𝒜 f hf 1))
      (fun i ↦ pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i))) := by
  let _ := coefficientSection_evaluation_epi 𝒜 f hf hcover
  exact ModuleGlobalEvaluationPullback.evaluation_epi p (line 𝒜 f hf 1)
    (coefficientSection 𝒜 f hf)

/-- Maps from the actual pullback are determined by the original coordinate sections. -/
theorem coefficientSection_pullback_hom_ext
    (hcover : (⨆ i, chart 𝒜 f i) = ⊤) {X : Scheme} (p : X ⟶ Proj 𝒜)
    {M : X.Modules} (a b : (pullback p).obj (line 𝒜 f hf 1) ⟶ M)
    (he : ∀ i, a.app ⊤ (pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i)) =
      b.app ⊤ (pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i))) : a = b := by
  let s := fun i ↦ pullGlobal p (line 𝒜 f hf 1) (coefficientSection 𝒜 f hf i)
  let _ := coefficientSection_pullback_evaluation_epi 𝒜 f hf hcover p
  apply (cancel_epi (ProjectiveSpace.globalEvaluation _ s)).mp
  apply CategoryTheory.Limits.Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan ι)
  intro i
  change SheafOfModules.ιFree i ≫ _ ≫ a = SheafOfModules.ιFree i ≫ _ ≫ b
  rw [← Category.assoc, ModuleGlobalEvaluationPullback.evaluation_generator,
    ← Category.assoc, ModuleGlobalEvaluationPullback.evaluation_generator]
  apply globalSection_hom_ext
  change a.app ⊤ ((globalSectionHom _ (s i)).app ⊤ (1 : Γ(X, ⊤))) =
    b.app ⊤ ((globalSectionHom _ (s i)).app ⊤ (1 : Γ(X, ⊤)))
  rw [globalSectionHom_top]
  exact he i

end FLT.Mazur.GradedProjLine
