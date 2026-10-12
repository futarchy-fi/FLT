/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOpenChartCoherence

/-!
# Full ambient projections on common Grassmannian chart opens

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


include h in
/-- Each subopen coordinate retains its original base map. -/
theorem coordinate_base (j : J) (U : X.Opens) (hj : U ≤ (i j).opensRange) :
    coordinate (i j) U hj ≫ Spec.algebraMap R (A j) =
      U.ι ≫ f ≫ ambientGrassmannianStructure R M κ d := by
  rw [← (a j).property, ← h j, ← Category.assoc, ← Category.assoc, coordinate_comp, Category.assoc]

attribute [local irreducible] grassmannianSchemeQuotientMap

/-- The entire original quotient projection on a common open of the source. -/
@[irreducible] def subopenProjection (j : J) (U : X.Opens) (hj : U ≤ (i j).opensRange) :
    grassmannianSchemeAmbient (M := M) (U.ι ≫ f ≫ ambientGrassmannianStructure R M κ d) ⟶
      (pullback (coordinate (i j) U hj)).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint (a j).val (a j).property)) :=
  grassmannianSchemeQuotientMap _ _ (coordinate_base f A i a h j U hj)
    (ambientMorphismPoint (a j).val (a j).property)

/-- Each original subopen projection is an epimorphism. -/
instance subopenProjection_epi (j : J) (U : X.Opens) (hj : U ≤ (i j).opensRange) :
    Epi (subopenProjection f A i a h j U hj) := by
  delta subopenProjection
  infer_instance

/-- The actual transition preserves the full ambient projection on every common subopen. -/
@[reassoc] theorem subopenIso_projection (j k : J) (U : X.Opens)
    (hj : U ≤ (i j).opensRange) (hk : U ≤ (i k).opensRange) :
    subopenProjection f A i a h j U hj ≫
        (subopenIso b hκ f (fun j ↦ .of (A j)) i a h j k U hj hk).hom =
      subopenProjection f A i a h k U hk := by
  delta subopenProjection subopenIso
  exact overlapIso_projection b hκ (a j) (a k) _ _ _ _ _ _

end FLT.Mazur.GrassmannianOpenChartDescent
