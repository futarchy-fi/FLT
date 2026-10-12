/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeQuotientRefinement
public import FLT.Mazur.GrassmannianWholeOverlapCocycle

/-!
# Geometric refinement of whole-overlap transitions

The original epi projection forces the transition constructed on an arbitrary
further scheme to agree with the pullback of the original overlap transition.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOverlapAffineTransition
open GrassmannianChart GrassmannianOverlapAffineCoordinates SheafPullbackPathComparison
universe u
variable {R A B M ι κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable (a : {a : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A})
variable (c : {c : Spec (.of B) ⟶ ambientGrassmannianScheme R M κ d //
  c ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R B})
variable {T X : Scheme.{u}} (p : X ⟶ Spec (.of A)) (q : X ⟶ Spec (.of B))
  (w : p ≫ a.val = q ≫ c.val) (z : T ⟶ X)
  (p' : T ⟶ Spec (.of A)) (q' : T ⟶ Spec (.of B))
  (hp : z ≫ p = p') (hq : z ≫ q = q') (w' : p' ≫ a.val = q' ≫ c.val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso
attribute [local irreducible] grassmannianSchemeQuotientMap comparison

/-- Actual whole-overlap transitions commute with arbitrary geometric refinement. -/
theorem overlapIso_refines :
    (pullback z).map (overlapIso b hκ a c p q w).hom ≫
        (comparison z q q' hq).hom.app (grassmannianQuotientSheaf
          (ambientMorphismPoint c.val c.property)) =
      (comparison z p p' hp).hom.app (grassmannianQuotientSheaf
          (ambientMorphismPoint a.val a.property)) ≫
        (overlapIso b hκ a c p' q' w').hom := by
  let β := p ≫ Spec.algebraMap R A
  let β' := z ≫ β
  have hbq : q ≫ Spec.algebraMap R B = β := (base_eq a c p q w).symm
  have hbp : p' ≫ Spec.algebraMap R A = β' := by rw [← hp, Category.assoc]
  have hbq' : q' ≫ Spec.algebraMap R B = β' := by
    rw [← hq, Category.assoc, hbq]
  apply (cancel_epi ((pullback z).map
    (grassmannianSchemeQuotientMap β p rfl (ambientMorphismPoint a.val a.property)))).mp
  rw [← Category.assoc, ← Functor.map_comp, overlapIso_projection b hκ a c p q w β rfl hbq]
  rw [grassmannianSchemeQuotientMap_refines z β β' rfl q q' hbq hq hbq']
  conv_rhs => rw [← Category.assoc]
  rw [grassmannianSchemeQuotientMap_refines z β β' rfl p p' rfl hp hbp,
    Category.assoc, overlapIso_projection b hκ a c p' q' w' β' hbp hbq']

end FLT.Mazur.GrassmannianOverlapAffineTransition
