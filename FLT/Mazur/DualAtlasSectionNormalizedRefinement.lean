/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualAtlasSectionChartPoints
public import FLT.Mazur.AffineSectionLineCoefficientMap

/-!
# Normalized point squares from an actual dual atlas section

When two actual atlas chart points are expressed by normalized lines,
their genuine restriction square implies the coefficient-level dual
transition equality. The projective coefficient open immersion is cancelled,
so the conclusion is the precise square needed for line compatibility.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.DualAtlasSectionChartPoints
open FCurve AffineFiniteFreeAtlas LocallyFreeDualProjectiveAtlas NormalizedSectionLine
open FiniteFreeChartTransitions
variable {X : Scheme.{u}} (M : X.Modules) (hM : LocallyFiniteFree M)
variable (s : X ⟶ space M hM) (hs : s ≫ projection M hM = 𝟙 X)

/-- Genuine normalized atlas points satisfy the actual dual transition square on refinement. -/
lemma normalized_point_refinement {i j : Index M} (h : i ≤ j)
    (a : coordinates M i) (b : coordinates M j)
    (L : Chart Γ(i.val.toScheme, ⊤) (coordinates M i) a)
    (N : Chart Γ(j.val.toScheme, ⊤) (coordinates M j) b)
    (hi : point M hM s hs i = ProjectiveSpace.affineSectionLinePoint (.id _) a L)
    (hj : point M hM s hs j = ProjectiveSpace.affineSectionLinePoint (.id _) b N) :
    ProjectiveSpace.sectionLinePoint Γ(i.val.toScheme, ⊤) (coordinates M i) (.id _) a L ≫
        (dualProjectiveTransition M le_rfl h (chart M i) (chart M j)).hom =
      ProjectiveSpace.sectionLinePoint Γ(i.val.toScheme, ⊤) (coordinates M j) (.id _) b
        (baseChange (X.homOfLE h).appTop.hom b N) := by
  have ht := point_refinement M hM s hs h
  rw [hi, hj, ProjectiveSpace.affineSectionLinePoint_pullback, dualChartInclusion] at ht
  simp only [RingHom.comp_id] at ht
  have hc := ProjectiveSpace.affineSectionLinePoint_coefficientMap
    (X.homOfLE h).appTop.hom (RingHom.id Γ(i.val.toScheme, ⊤)) b
    (baseChange (X.homOfLE h).appTop.hom b N)
  simp only [RingHom.id_comp] at hc
  have he : ProjectiveSpace.affineSectionLinePoint (.id _) a L ≫
      (dualProjectiveTransition M le_rfl h (chart M i) (chart M j)).hom =
        ProjectiveSpace.affineSectionLinePoint (.id _) b
          (baseChange (X.homOfLE h).appTop.hom b N) := by
    apply (cancel_mono (ProjectiveSpace.coefficientMap
      (X.homOfLE h).appTop.hom (coordinates M j))).mp
    exact (Category.assoc _ _ _).trans (ht.symm.trans hc.symm)
  apply (cancel_epi i.val.toScheme.isoSpec.hom).mp
  simpa only [ProjectiveSpace.affineSectionLinePoint, Category.assoc] using he

end FLT.Mazur.DualAtlasSectionChartPoints
