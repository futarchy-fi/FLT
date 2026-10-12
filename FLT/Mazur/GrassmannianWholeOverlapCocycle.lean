/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianWholeOverlapProjection

/-!
# Whole-overlap cocycles from the original ambient quotient

All three original projections share one base ambient sheaf. Its epi
projection forces the actual whole-overlap transitions to satisfy the
cocycle and identity laws on an arbitrary scheme.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianOverlapAffineTransition
open GrassmannianChart GrassmannianOverlapAffineCoordinates
universe u
variable {R A B C M ι κ : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable (a : {a : Spec (.of A) ⟶ ambientGrassmannianScheme R M κ d //
  a ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R A})
variable (c : {c : Spec (.of B) ⟶ ambientGrassmannianScheme R M κ d //
  c ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R B})
variable (e : {e : Spec (.of C) ⟶ ambientGrassmannianScheme R M κ d //
  e ≫ ambientGrassmannianStructure R M κ d = Spec.algebraMap R C})
variable {X : Scheme.{u}} (p : X ⟶ Spec (.of A)) (q : X ⟶ Spec (.of B))
  (r : X ⟶ Spec (.of C)) (w : p ≫ a.val = q ≫ c.val) (v : q ≫ c.val = r ≫ e.val)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf overlapIso
attribute [local irreducible] grassmannianSchemeQuotientMap

/-- The actual quotient transitions satisfy the cocycle on the entire arbitrary overlap. -/
theorem overlapIso_cocycle :
    (overlapIso b hκ a c p q w).hom ≫ (overlapIso b hκ c e q r v).hom =
      (overlapIso b hκ a e p r (w.trans v)).hom := by
  let β := p ≫ Spec.algebraMap R A
  have hq : q ≫ Spec.algebraMap R B = β := (base_eq a c p q w).symm
  have hr : r ≫ Spec.algebraMap R C = β := (base_eq a e p r (w.trans v)).symm
  apply (cancel_epi
    (grassmannianSchemeQuotientMap β p rfl (ambientMorphismPoint a.val a.property))).mp
  rw [← Category.assoc, overlapIso_projection b hκ a c p q w β rfl hq,
    overlapIso_projection b hκ c e q r v β hq hr,
    overlapIso_projection b hκ a e p r (w.trans v) β rfl hr]

/-- A chart compared with itself has the identity quotient transition on the whole source. -/
theorem overlapIso_self : (overlapIso b hκ a a p p rfl).hom = 𝟙 _ := by
  apply (cancel_epi (grassmannianSchemeQuotientMap (p ≫ Spec.algebraMap R A) p rfl
    (ambientMorphismPoint a.val a.property))).mp
  rw [Category.comp_id]
  exact overlapIso_projection b hκ a a p p rfl (p ≫ Spec.algebraMap R A) rfl rfl

/-- Reversing an entire-overlap transition gives its genuine inverse. -/
theorem overlapIso_reverse :
    (overlapIso b hκ c a q p w.symm).hom = (overlapIso b hκ a c p q w).inv := by
  apply (cancel_epi (overlapIso b hκ a c p q w).hom).mp
  rw [overlapIso_cocycle b hκ a c a p q p w w.symm, overlapIso_self, Iso.hom_inv_id]

end FLT.Mazur.GrassmannianOverlapAffineTransition
