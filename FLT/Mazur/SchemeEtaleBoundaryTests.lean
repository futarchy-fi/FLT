/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOpenSectionDescent

/-!
# Boundary equality detected by one etale source cover

Agreement on all scheme-valued tests of an etale chart proves equality on the
entire original boundary. The proof uses the actual scheme pullback and detects
regular functions, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeEffectiveEpiSections
variable {X Y Z : Scheme.{u}} (j : Z ⟶ X) [Etale j] [Surjective j] (g : Y ⟶ X)

/-- Tests of a surjective etale chart detect the exact original boundary function. -/
theorem boundary_eq_of_etale_tests (s : Γ(X, ⊤)) (t : Γ(Y, ⊤))
    (h : ∀ (T : Scheme.{u}) (a : T ⟶ Z) (b : T ⟶ Y),
      a ≫ j = b ≫ g → a.appTop (j.appTop s) = b.appTop t) :
    g.appTop s = t := by
  apply appTop_injective (pullback.fst g j)
  have he := h (pullback g j) (pullback.snd g j) (pullback.fst g j)
    pullback.condition.symm
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop] at he ⊢
  exact (congrArg (fun z : pullback g j ⟶ X ↦ z.appTop s)
    (pullback.condition (f := g) (g := j))).trans he

end FLT.Mazur.SchemeEffectiveEpiSections
