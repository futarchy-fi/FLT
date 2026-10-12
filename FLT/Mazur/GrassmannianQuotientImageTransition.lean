/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianTypedOpenChartComparisons

/-!
# Ambient transitions of original Grassmannian quotient charts

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

/-- The entire original quotient comparison on the actual intersection of chart images. -/
@[irreducible] def quotientImageTransition (j k : J) :
    ((pushforward (i j)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property))).over
        ((i j).opensRange ⊓ (i k).opensRange) ≅
    ((pushforward (i k)).obj
      (grassmannianQuotientSheaf (ambientMorphismPoint (a k).val (a k).property))).over
        ((i j).opensRange ⊓ (i k).opensRange) :=
  transition (i j) (i k) _ inf_le_left inf_le_right
    (typedSubopenIso b hκ f A i a h j k _ inf_le_left inf_le_right)

/-- Restricting the actual image transition recovers the independently constructed comparison. -/
theorem quotientImageTransition_app (j k : J) (V : X.Opens)
    (hj : V ≤ (i j).opensRange) (hk : V ≤ (i k).opensRange) :
    localApp (quotientImageTransition b hκ f A i a h j k).hom (le_inf hj hk) =
      localApp (transition (i j) (i k) V hj hk
        (typedSubopenIso b hκ f A i a h j k V hj hk)).hom le_rfl := by
  delta quotientImageTransition
  exact (transition_refine_app (i j) (i k) _ inf_le_left inf_le_right
    (typedSubopenIso b hκ f A i a h j k _ inf_le_left inf_le_right)
    V (le_inf hj hk) (typedSubopenIso b hκ f A i a h j k V hj hk)
    (typedSubopenIso_refines b hκ f A i a h j k _ V
      (le_inf hj hk) inf_le_left inf_le_right) V le_rfl).symm

end FLT.Mazur.GrassmannianOpenChartDescent
