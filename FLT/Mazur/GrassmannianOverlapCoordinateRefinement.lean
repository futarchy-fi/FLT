/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapAffineTransition
public import FLT.Mazur.GrassmannianNamedRefinement
public import FLT.Mazur.GrassmannianOverlapDirectRefinement

/-!
# Refinement coherence on arbitrary overlap tests

The actual quotient transitions on affine tests commute with every further
affine refinement, using the original coefficient algebra maps.
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

attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf
attribute [local irreducible] grassmannianQuotientSheafTransition testIso coordinateMap
attribute [local irreducible] comparison pullbackComp pullbackCongr

variable {D E : CommRingCat.{u}} (z : Spec D ⟶ X) (z' : Spec E ⟶ X)
  (α : D ⟶ E) (h : Spec.map α ≫ z = z')

include h in
/-- The first coordinate triangle on an affine refinement. -/
theorem left_refinement_square :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    Spec.map α ≫ Spec.map (CommRingCat.ofHom (left (R := R) p z).toRingHom) =
      Spec.map (CommRingCat.ofHom (left (R := R) p z').toRingHom) := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  rw [left_spec, left_spec, ← Category.assoc, h]

include h in
/-- The second coordinate triangle on the same affine refinement. -/
theorem right_refinement_square :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    Spec.map α ≫
        Spec.map (CommRingCat.ofHom (right p q (base_eq a c p q w) z).toRingHom) =
      Spec.map (CommRingCat.ofHom (right p q (base_eq a c p q w) z').toRingHom) := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  rw [right_spec, right_spec, ← Category.assoc, h]

/-- The original transitions satisfy named-coordinate refinement with the original ring map. -/
theorem named_refines :
    let _ := coefficientAlgebra (R := R) p z
    let _ := coefficientAlgebra (R := R) p z'
    grassmannianNamedTransitionRefines
      (left (R := R) p z) (right p q (base_eq a c p q w) z)
      (directRefine (R := R) p z z' α h)
      (left (R := R) p z') (right p q (base_eq a c p q w) z')
      (ambientMorphismPoint a.val a.property) (ambientMorphismPoint c.val c.property)
      (point_eq b hκ a c p q w z) (point_eq b hκ a c p q w z')
      (left_refinement_square p z z' α h)
      (right_refinement_square a c p q w z z' α h) := by
  let _ := coefficientAlgebra (R := R) p z
  let _ := coefficientAlgebra (R := R) p z'
  exact grassmannianNamedTransitionRefines_of_eq
    (left (R := R) p z) (right p q (base_eq a c p q w) z)
    (directRefine (R := R) p z z' α h)
    (left (R := R) p z') (right p q (base_eq a c p q w) z')
    (directRefine_left p z z' α h) (directRefine_right p q (base_eq a c p q w) z z' α h)
    (ambientMorphismPoint a.val a.property) (ambientMorphismPoint c.val c.property)
    (point_eq b hκ a c p q w z) (point_eq b hκ a c p q w z')
    (left_refinement_square p z z' α h)
    (right_refinement_square a c p q w z z' α h)

end FLT.Mazur.GrassmannianOverlapAffineTransition
