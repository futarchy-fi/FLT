/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianQuotientImageTransition
public import FLT.Mazur.GrassmannianAmbientChartConeCoordinate
public import FLT.Mazur.ModuleSheafOpenTransitionProjection

/-!
# Compatibility of the actual global ambient chart maps

The original transition preserves the entire quotient projection. Coordinate
recovery therefore makes the actual ambient adjoints a compatible cone.
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

/-- The full original chart comparisons preserve the actual ambient adjoints. -/
@[reassoc] theorem quotientAmbientChartAdjoint_transition (j k : J) :
    (quotientAmbientChartAdjoint f A i a h j).over
        ((i j).opensRange ⊓ (i k).opensRange) ≫
      (quotientImageTransition b hκ f A i a h j k).hom =
    (quotientAmbientChartAdjoint f A i a h k).over
      ((i j).opensRange ⊓ (i k).opensRange) := by
  delta quotientImageTransition
  apply transition_projection
  rw [← Category.assoc, quotientAmbientChartAdjoint_coordinate,
    quotientAmbientChartAdjoint_coordinate, Category.assoc]
  delta typedSubopenIso
  rw [subopenIso_projection]

end FLT.Mazur.GrassmannianOpenChartDescent
