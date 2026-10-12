/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianOverlapTestRefinement
public import FLT.Mazur.AffineOpenCoverTestRecovery

/-!
# Quotient transitions on entire arbitrary overlaps

The refinement-compatible affine-test transitions glue on the canonical affine
open cover and recover their original maps on every affine test.
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

/-- Glue the actual quotient transitions on the whole arbitrary overlap. -/
def overlapIso :
    (pullback p).obj (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property)) ≅
      (pullback q).obj (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property)) :=
  SheafPullbackRefinementLaw.glueIso X.affineOpenCover
    (fun z ↦ (testIso b hκ a c p q w z).hom)
    (fun z z' α h ↦ testIso_refines b hκ a c p q w z z' α h)
    (fun _ ↦ inferInstance)

/-- Every affine test recovers the originally constructed quotient transition. -/
theorem overlapIso_test {D : CommRingCat.{u}} (z : Spec D ⟶ X) :
    (pullback z).map (overlapIso b hκ a c p q w).hom =
      (testIso b hκ a c p q w z).hom :=
  SheafPullbackRefinementLaw.glueIso_test X.affineOpenCover
    (fun z ↦ (testIso b hκ a c p q w z).hom)
    (fun z z' α h ↦ testIso_refines b hκ a c p q w z z' α h)
    (fun _ ↦ inferInstance) z

/-- The glued transition is uniquely determined by its maps on the original affine tests. -/
theorem overlapIso_unique
    (e : (pullback p).obj (grassmannianQuotientSheaf (ambientMorphismPoint a.val a.property)) ⟶
      (pullback q).obj (grassmannianQuotientSheaf (ambientMorphismPoint c.val c.property)))
    (he : ∀ {D : CommRingCat.{u}} (z : Spec D ⟶ X),
      (pullback z).map e = (testIso b hκ a c p q w z).hom) :
    e = (overlapIso b hκ a c p q w).hom := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec (X.affineOpenCover.X i)) X.affineOpenCover.f
    (AffineOpenCoverCommonRefinement.jointly_surjective X.affineOpenCover)
  intro i
  rw [he, overlapIso_test]

end FLT.Mazur.GrassmannianOverlapAffineTransition
