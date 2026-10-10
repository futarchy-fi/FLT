/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTensorSections
public import FLT.Mazur.ModuleGlobalEvaluationPullback
public import FLT.Mazur.SectionGradedMultiplication

/-!
# Twisted evaluation as a finite sum of actual section products

The finite free coordinates identify the original twisted evaluation with
sums of pure tensors. After the specified exponent-addition isomorphism,
surjectivity gives generation by the original graded multiplication.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ProjectiveSpace ModuleSheafTensor ModuleLineBundleTensorPullback

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme} {I : Type}

/-- Evaluation sends each original free generator at one to the prescribed global section. -/
lemma globalEvaluation_generator_one (M : X.Modules) (s : I → Γ(M, ⊤)) (i : I) :
    (Hom.app (X := X) (globalEvaluation M s) ⊤)
      ((SheafOfModules.ιFree (R := X.ringCatSheaf) i).val.app (.op ⊤)
        (1 : Γ(X, ⊤))) = s i := by
  have he := congrArg (fun f : structureModule X ⟶ M ↦ f.app ⊤ (1 : Γ(X, ⊤)))
    (ModuleGlobalEvaluationPullback.evaluation_generator M s i)
  exact he.trans (globalSectionHom_top M (s i))

variable [Fintype I]

/-- Every value of twisted evaluation is a finite sum with the specified left sections. -/
theorem twistedEvaluation_section_sum (M N : X.Modules) (s : I → Γ(M, ⊤))
    (u : Γ(tensor (SheafOfModules.free I) N, ⊤)) :
    ∃ t : I → Γ(N, ⊤),
      (ModuleSheafTensor.map (globalEvaluation M s) (𝟙 N)).app ⊤ u =
        ∑ i, pure M N ⊤ (s i) (t i) := by
  obtain ⟨t, rfl⟩ := freeTensorSection_sum N I ⊤ u
  refine ⟨t, ?_⟩
  simp only [map_sum, map_pure, globalEvaluation_generator_one,
    Hom.id_app, ConcreteCategory.id_apply]

/-- Surjectivity of the original twist map gives sums of actual homogeneous products. -/
theorem section_mul_sum_of_twistedEvaluation_surjective (L : X.Modules) (a d : ℕ)
    (s : I → Γ(tensorPower L a, ⊤))
    (hs : Function.Surjective ((ModuleSheafTensor.map
      (globalEvaluation (tensorPower L a) s) (𝟙 (tensorPower L d))).app ⊤))
    (v : Γ(tensorPower L (a + d), ⊤)) :
    ∃ t : I → Γ(tensorPower L d, ⊤),
      v = ∑ i, SectionGradedMultiplication.mul L ⊤ a d (s i) (t i) := by
  obtain ⟨u, hu⟩ := hs ((tensorPowerAddIso L a d).inv.app ⊤ v)
  obtain ⟨t, ht⟩ := twistedEvaluation_section_sum _ _ s u
  refine ⟨t, ?_⟩
  have he := congrArg ((tensorPowerAddIso L a d).hom.app ⊤) (hu.symm.trans ht)
  simpa only [map_sum, ← SectionGradedMultiplication.mul_apply,
    ← ConcreteCategory.comp_apply, ← Hom.comp_app, Iso.inv_hom_id,
    Hom.id_app, ConcreteCategory.id_apply] using he

end FLT.Mazur.FCurve
