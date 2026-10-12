/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianWholeOverlapTransition

/-!
# Original quotient projections on overlap tests

The glued transition preserves the full original ambient quotient projection
on each affine test. Each such original projection remains an epimorphism.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOverlapAffineTransition
open GrassmannianChart GrassmannianOverlapAffineCoordinates
open SheafPullbackPathComparison SheafPullbackCoordinateRefinement
universe u
variable {R A B M ι κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable (a : {a : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A})
variable (c : {c : Spec (.of B) ⟶ ambientGrassmannianScheme R M κ d //
  c ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R B})
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) (q : X ⟶ Spec (.of B))
  (w : p ≫ a.val = q ≫ c.val)

attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf testIso
attribute [local irreducible] grassmannianRefinedQuotientMap coordinateMap comparison
variable {D : CommRingCat.{u}} (z : Spec D ⟶ X)

/-- The original first quotient projection expressed on the actual affine test. -/
def leftProjection :
    let _ := coefficientAlgebra (R := R) p z
    tilde (ModuleCat.of D (D ⊗[R] M)) ⟶
      (pullback z).obj ((pullback p).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property))) := by
  let _ := coefficientAlgebra (R := R) p z
  exact grassmannianRefinedQuotientMap (left (R := R) p z)
    (ambientMorphismPoint a.val a.property) ≫
      (comparison z p _ (left_spec (R := R) p z).symm).inv.app _

/-- The second quotient projection uses the same original coefficient ambient module. -/
def rightProjection :
    let _ := coefficientAlgebra (R := R) p z
    tilde (ModuleCat.of D (D ⊗[R] M)) ⟶
      (pullback z).obj ((pullback q).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property))) := by
  let _ := coefficientAlgebra (R := R) p z
  exact grassmannianRefinedQuotientMap (right p q (base_eq a c p q w) z)
    (ambientMorphismPoint c.val c.property) ≫
      (comparison z q _ (right_spec p q (base_eq a c p q w) z).symm).inv.app _

/-- The first original ambient quotient remains epi after coordinate normalization. -/
instance leftProjection_epi :
    let _ := coefficientAlgebra (R := R) p z
    Epi (leftProjection a p z) := by
  let _ := coefficientAlgebra (R := R) p z
  dsimp only [leftProjection]
  exact epi_comp (grassmannianRefinedQuotientMap (left (R := R) p z)
    (ambientMorphismPoint a.val a.property))
    ((comparison z p _ (left_spec (R := R) p z).symm).app _).inv

private theorem projection_conjugate {C : Type*} [Category C]
    {V A B A' B' : C} (s : A ≅ A') (t : B ≅ B')
    (l : V ⟶ A') (r : V ⟶ B') (e : A' ⟶ B') (he : l ≫ e = r) :
    (l ≫ s.inv) ≫ (s.hom ≫ e ≫ t.inv) = r ≫ t.inv := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, he]

/-- The actual affine-test transition preserves the full original quotient projection. -/
theorem testIso_projection :
    let _ := coefficientAlgebra (R := R) p z
    leftProjection a p z ≫ (testIso b hκ a c p q w z).hom =
      rightProjection a c p q w z := by
  let _ := coefficientAlgebra (R := R) p z
  rw [testIso_hom]
  dsimp only [leftProjection, rightProjection]
  unfold coordinateMap
  exact projection_conjugate
    ((comparison z p _ (left_spec (R := R) p z).symm).app _)
    ((comparison z q _ (right_spec p q (base_eq a c p q w) z).symm).app _)
    (grassmannianRefinedQuotientMap (left (R := R) p z) _)
    (grassmannianRefinedQuotientMap (right p q (base_eq a c p q w) z) _)
    (grassmannianQuotientSheafTransition (left (R := R) p z)
      (right p q (base_eq a c p q w) z) _ _ (point_eq b hκ a c p q w z)).hom
    (grassmannianQuotientSheafTransition_projection _ _ _ _ _)

/-- The whole-overlap transition preserves the original projection on every affine test. -/
theorem overlapIso_projection_test :
    let _ := coefficientAlgebra (R := R) p z
    leftProjection a p z ≫ (pullback z).map (overlapIso b hκ a c p q w).hom =
      rightProjection a c p q w z := by
  let _ := coefficientAlgebra (R := R) p z
  rw [overlapIso_test]
  exact testIso_projection b hκ a c p q w z

/-- The original ambient projections determine the entire overlap transition uniquely. -/
theorem overlapIso_unique_of_projection
    (e : (pullback p).obj (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property)) ⟶
      (pullback q).obj (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property)))
    (he : ∀ {D : CommRingCat.{u}} (z : Spec D ⟶ X),
      let _ := coefficientAlgebra (R := R) p z
      leftProjection a p z ≫ (pullback z).map e = rightProjection a c p q w z) :
    e = (overlapIso b hκ a c p q w).hom := by
  apply overlapIso_unique b hκ a c p q w e
  intro D z
  let _ := coefficientAlgebra (R := R) p z
  apply (cancel_epi (leftProjection a p z)).mp
  exact (he z).trans (testIso_projection b hκ a c p q w z).symm

end FLT.Mazur.GrassmannianOverlapAffineTransition
