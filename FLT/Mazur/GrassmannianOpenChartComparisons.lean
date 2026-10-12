/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianWholeOverlapRefinement
public import FLT.Mazur.ModuleSheafGeometricOpenCocycle

/-!
# Actual quotient-sheaf descent on Grassmannian affine charts

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
variable {J : Type u} (A : J → CommRingCat.{u}) [∀ j, Algebra R (A j)]
  (i : ∀ j, Spec (A j) ⟶ X) [∀ j, IsOpenImmersion (i j)]
variable (a : ∀ j, {a : Spec (A j) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R (A j)})
  (h : ∀ j, i j ≫ f = (a j).val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso

include h in
/-- Coordinates on any common open retain the same original Grassmannian morphism. -/
theorem coordinate_eq (j k : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange) :
    coordinate (i j) U hj ≫ (a j).val = coordinate (i k) U hk ≫ (a k).val := by
  rw [← h j, ← h k, ← Category.assoc, coordinate_comp,
    ← Category.assoc, coordinate_comp]

/-- The actual quotient comparison on an arbitrary common subopen of two affine charts. -/
@[irreducible] def subopenIso (j k : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange) :
    (pullback (coordinate (i j) U hj)).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) ≅
      (pullback (coordinate (i k) U hk)).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint (a k).val (a k).property)) :=
  overlapIso b hκ (a j) (a k) (coordinate (i j) U hj) (coordinate (i k) U hk)
    (coordinate_eq f A i a h j k U hj hk)

end FLT.Mazur.GrassmannianOpenChartDescent
