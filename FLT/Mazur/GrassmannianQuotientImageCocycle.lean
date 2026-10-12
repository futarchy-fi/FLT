/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageTransition

/-!
# Section cocycles for original Grassmannian quotient charts

An arbitrary morphism to the Grassmannian gives compatible quotient sheaves on
its affine open charts. The whole-overlap comparisons satisfy the geometric
refinement and cocycle hypotheses of module-sheaf gluing.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOpenChartDescent
open GrassmannianChart GrassmannianOverlapAffineTransition
open ModuleSheafOpenImageChart SheafPullbackPathComparison
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (f : X ⟶ ambientGrassmannianScheme R M κ d)
variable {J : Type u} (A : J → Type u) [∀ j, CommRing (A j)] [∀ j, Algebra R (A j)]
  (i : ∀ j, Spec (.of (A j)) ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, {a : Spec (.of (A j)) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h : ∀ j, i j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso

open ModuleSheafOpenOverlapTransition ModuleSheafMorphismGluing
attribute [local irreducible] Scheme.Modules.pushforward

/-- The actual image transitions obey the cocycle on every common open section. -/
theorem quotientImageTransition_cocycle (j k l : J) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange)
    (hl : V ≤ (i l).opensRange)
    (s : Γ((pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)), V)) :
    localApp (quotientImageTransition b hκ f A i a h k l).hom (le_inf hk hl)
        (localApp (quotientImageTransition b hκ f A i a h j k).hom (le_inf hj hk) s) =
      localApp (quotientImageTransition b hκ f A i a h j l).hom (le_inf hj hl) s := by
  rw [quotientImageTransition_app, quotientImageTransition_app, quotientImageTransition_app]
  exact transition_cocycle_app (i j) (i k) V hj hk
    (typedSubopenIso b hκ f A i a h j k V hj hk) (i l) hl
    (typedSubopenIso b hκ f A i a h k l V hk hl)
    (typedSubopenIso b hκ f A i a h j l V hj hl)
    (typedSubopenIso_cocycle b hκ f A i a h j k l V hj hk hl) V le_rfl s

/-- The original section cocycle in the evaluator consumed by chart gluing. -/
theorem quotientImageTransition_cocycle_eval (j k l : J) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange)
    (hl : V ≤ (i l).opensRange)
    (s : Γ((pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)), V)) :
    localEval (quotientImageTransition b hκ f A i a h k l).hom (le_inf hk hl)
        (localEval (quotientImageTransition b hκ f A i a h j k).hom (le_inf hj hk) s) =
      localEval (quotientImageTransition b hκ f A i a h j l).hom (le_inf hj hl) s := by
  simpa only [localEval] using
    quotientImageTransition_cocycle b hκ f A i a h j k l V hj hk hl s

end FLT.Mazur.GrassmannianOpenChartDescent
