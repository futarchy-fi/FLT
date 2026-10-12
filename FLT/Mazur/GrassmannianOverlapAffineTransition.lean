/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapAffineCoordinates
public import FLT.Mazur.GrassmannianMorphismSheafTransition
public import FLT.Mazur.SheafPullbackCoordinateRefinement

/-!
# Quotient transitions on affine tests of arbitrary overlaps

Coincidence of the original Grassmannian maps produces an isomorphism between
actual pulled-back quotient sheaves on every affine test of the overlap.
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

include w in
/-- The original coincidence also identifies the coefficient structure maps. -/
theorem base_eq : p ≫ Spec.algebraMap R A = q ≫ Spec.algebraMap R B := by
  rw [← a.property, ← c.property, ← Category.assoc, ← Category.assoc, w]

variable {D : CommRingCat.{u}} (z : Spec D ⟶ X)

include b hκ w in
/-- The full recovered quotient relations agree on each original affine test. -/
theorem point_eq :
    let _ := coefficientAlgebra (R := R) p z
    Module.Grassmannian.map (left (R := R) p z)
        (ambientMorphismPoint a.val a.property) =
      Module.Grassmannian.map (right p q (base_eq a c p q w) z)
        (ambientMorphismPoint c.val c.property) := by
  let _ := coefficientAlgebra (R := R) p z
  apply ambientMorphismPoint_commonRefinement b hκ a c
  rw [left_spec, right_spec, Category.assoc, Category.assoc, w]

attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf
attribute [local irreducible] grassmannianQuotientSheafTransition

/-- The actual quotient transition expressed as pullbacks along the affine test. -/
def testIso :
    (pullback z).obj ((pullback p).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property))) ≅
      (pullback z).obj ((pullback q).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property))) := by
  let _ := coefficientAlgebra (R := R) p z
  exact (comparison z p _ (left_spec (R := R) p z).symm).app _ ≪≫
    grassmannianQuotientSheafTransition (left (R := R) p z)
      (right p q (base_eq a c p q w) z) _ _ (point_eq b hκ a c p q w z) ≪≫
        ((comparison z q _ (right_spec p q (base_eq a c p q w) z).symm).app _).symm

/-- The affine-test isomorphism has the normalized coordinate map used for refinement. -/
theorem testIso_hom :
    let _ := coefficientAlgebra (R := R) p z
    (testIso b hκ a c p q w z).hom =
      coordinateMap z p q _ _ (left_spec (R := R) p z).symm
        (right_spec p q (base_eq a c p q w) z).symm
        (grassmannianQuotientSheafTransition (left (R := R) p z)
          (right p q (base_eq a c p q w) z) _ _ (point_eq b hκ a c p q w z)).hom := rfl

end FLT.Mazur.GrassmannianOverlapAffineTransition
