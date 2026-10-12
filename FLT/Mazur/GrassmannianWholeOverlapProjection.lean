/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeQuotientTest
public import FLT.Mazur.GrassmannianOverlapTestProjection

/-!
# Original ambient projections on entire overlaps

The actual whole-overlap transition preserves the normalized projection from
the single base ambient sheaf. The proof compares every affine test and uses
joint faithfulness of open pullback.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOverlapAffineTransition
open GrassmannianChart GrassmannianOverlapAffineCoordinates
open SheafPullbackPathComparison
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
variable (β : X ⟶ Spec (.of R)) (hp : p ≫ Spec.algebraMap R A = β)
  (hq : q ≫ Spec.algebraMap R B = β)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso
attribute [local irreducible] grassmannianSchemeQuotientMap grassmannianRefinedQuotientMap
attribute [local irreducible] comparison

/-- The global projection equation holds after every actual affine test pullback. -/
theorem overlapIso_projection_affine {D : CommRingCat.{u}} (z : Spec D ⟶ X) :
    (pullback z).map
      (grassmannianSchemeQuotientMap β p hp (ambientMorphismPoint a.val a.property) ≫
        (overlapIso b hκ a c p q w).hom) =
    (pullback z).map
      (grassmannianSchemeQuotientMap β q hq (ambientMorphismPoint c.val c.property)) := by
  let _ := coefficientAlgebra (R := R) p z
  have hz : z ≫ β = Spec.algebraMap R D := by
    rw [coefficientAlgebra_spec (R := R) p z, hp]
  apply (cancel_epi (grassmannianSchemeAmbientTestIso (M := M) β z hz).inv).mp
  rw [Functor.map_comp, ← Category.assoc,
    grassmannianSchemeQuotientMap_test β z hz p hp (left (R := R) p z)
      (left_spec (R := R) p z).symm,
    grassmannianSchemeQuotientMap_test β z hz q hq (right p q (base_eq a c p q w) z)
      (right_spec p q (base_eq a c p q w) z).symm]
  exact overlapIso_projection_test b hκ a c p q w z

/-- Global normalized projections agree across the actual whole-overlap transition. -/
theorem overlapIso_projection :
    grassmannianSchemeQuotientMap β p hp (ambientMorphismPoint a.val a.property) ≫
      (overlapIso b hκ a c p q w).hom =
    grassmannianSchemeQuotientMap β q hq (ambientMorphismPoint c.val c.property) := by
  apply ModuleSheafOpenImmersionGluing.hom_ext
    (fun i ↦ Spec (X.affineOpenCover.X i)) X.affineOpenCover.f
    (AffineOpenCoverCommonRefinement.jointly_surjective X.affineOpenCover)
  intro i
  exact overlapIso_projection_affine b hκ a c p q w β hp hq (X.affineOpenCover.f i)

end FLT.Mazur.GrassmannianOverlapAffineTransition
