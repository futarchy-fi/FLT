/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianAffinePointFunctor
public import FLT.Mazur.GrassmannianQuotientSheafTransition

/-!
# Sheaf transitions recovered from geometric affine overlap diagrams

Coincidence of the original scheme maps on a common affine refinement proves
equality of the entire recovered quotient relations. Consequently the actual
quotient sheaves have canonical transitions preserving the ambient projection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R A B C D M ι κ : Type u} [CommRing R] [CommRing A] [CommRing B]
  [CommRing C] [CommRing D] [Algebra R A] [Algebra R B] [Algebra R C]
  [Algebra R D] [AddCommGroup M] [Module R M] [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable (a : {a : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A})
variable (c : {c : Spec (.of B) ⟶ ambientGrassmannianScheme R M κ d //
  c ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R B})
variable (f : A →ₐ[R] D) (g : B →ₐ[R] D)
variable (w : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ a.val =
  Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c.val)

include b hκ w in
/-- A geometric common refinement identifies the full original recovered relations. -/
theorem ambientMorphismPoint_commonRefinement :
    Module.Grassmannian.map f (ambientMorphismPoint a.val a.property) =
      Module.Grassmannian.map g (ambientMorphismPoint c.val c.property) := by
  have h : ambientSchemePointMap f a = ambientSchemePointMap g c := Subtype.ext w
  have h' := congrArg (fun z ↦ ambientMorphismPoint z.val z.property) h
  rw [ambientMorphismPoint_natural b hκ f a, ambientMorphismPoint_natural b hκ g c] at h'
  exact h'

/-- The actual sheaf transition attached to an affine overlap diagram of scheme maps. -/
def ambientMorphismSheafTransition :
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property)) ≅
      (pullback (Spec.map (CommRingCat.ofHom g.toRingHom))).obj
        (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property)) :=
  grassmannianQuotientSheafTransition f g _ _
    (ambientMorphismPoint_commonRefinement b hκ a c f g w)

/-- The geometric transition preserves the whole ambient quotient projection. -/
@[reassoc] theorem ambientMorphismSheafTransition_projection :
    grassmannianRefinedQuotientMap f (ambientMorphismPoint a.val a.property) ≫
        (ambientMorphismSheafTransition b hκ a c f g w).hom =
      grassmannianRefinedQuotientMap g (ambientMorphismPoint c.val c.property) :=
  grassmannianQuotientSheafTransition_projection f g _ _ _

/-- Triple geometric coincidences imply the actual sheaf cocycle on the common refinement. -/
@[reassoc] theorem ambientMorphismSheafTransition_cocycle
    (e : {e : Spec (.of C) ⟶ ambientGrassmannianScheme R M κ d //
      e ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R C})
    (k : C →ₐ[R] D)
    (w' : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c.val =
      Spec.map (CommRingCat.ofHom k.toRingHom) ≫ e.val) :
    (ambientMorphismSheafTransition b hκ a c f g w).hom ≫
        (ambientMorphismSheafTransition b hκ c e g k w').hom =
      (ambientMorphismSheafTransition b hκ a e f k (w.trans w')).hom :=
  grassmannianQuotientSheafTransition_cocycle f g _ _ _ k _ _

/-- Every scheme pullback of an affine-refinement transition still preserves the projection. -/
@[reassoc] theorem ambientMorphismSheafTransition_pullback_projection
    {X : Scheme.{u}} (j : X ⟶ Spec (.of D)) :
    (pullback j).map
        (grassmannianRefinedQuotientMap f (ambientMorphismPoint a.val a.property)) ≫
      (pullback j).map (ambientMorphismSheafTransition b hκ a c f g w).hom =
        (pullback j).map
          (grassmannianRefinedQuotientMap g (ambientMorphismPoint c.val c.property)) := by
  rw [← Functor.map_comp, ambientMorphismSheafTransition_projection]

/-- The cocycle persists on arbitrary scheme tests of the common affine refinement. -/
@[reassoc] theorem ambientMorphismSheafTransition_pullback_cocycle
    {X : Scheme.{u}} (j : X ⟶ Spec (.of D))
    (e : {e : Spec (.of C) ⟶ ambientGrassmannianScheme R M κ d //
      e ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R C})
    (k : C →ₐ[R] D)
    (w' : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ c.val =
      Spec.map (CommRingCat.ofHom k.toRingHom) ≫ e.val) :
    (pullback j).map (ambientMorphismSheafTransition b hκ a c f g w).hom ≫
        (pullback j).map (ambientMorphismSheafTransition b hκ c e g k w').hom =
      (pullback j).map (ambientMorphismSheafTransition b hκ a e f k (w.trans w')).hom := by
  rw [← Functor.map_comp, ambientMorphismSheafTransition_cocycle]

end FLT.Mazur.GrassmannianChart
