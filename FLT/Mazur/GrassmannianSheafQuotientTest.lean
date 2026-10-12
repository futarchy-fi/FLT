/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSchemeQuotientTest
public import FLT.Mazur.GrassmannianQuotientSheafFaithful
public import FLT.Mazur.SheafPullbackAmbientTestRefinement

/-!
# Affine tests of arbitrary global ambient quotients

Coordinate projections of one global quotient commute with refinement. Local
original quotient presentations therefore retain their full projections on
arbitrary affine tests of intersections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
open SheafPullbackPathComparison SheafPullbackAmbientNormalization
universe u
variable {R A B M : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [AddCommGroup M] [Module R M] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
variable (i : Spec (.of A) ⟶ X) (hi : i ≫ β = Spec.algebraMap R A)
attribute [local irreducible] Scheme.Modules.pullback grassmannianAmbientSheafPullbackIso
  comparison grassmannianQuotientSheaf

/-- The full global quotient projection in the original affine ambient coordinates. -/
@[irreducible] def sheafQuotientTestMap :
    tilde (ModuleCat.of A (A ⊗[R] M)) ⟶ (pullback i).obj P :=
  (grassmannianSchemeAmbientTestIso β i hi).inv ≫ (pullback i).map p

/-- A global epimorphism gives an actual quotient on each affine test. -/
instance sheafQuotientTestMap_epi [Epi p] : Epi (sheafQuotientTestMap β p i hi) := by
  unfold sheafQuotientTestMap
  infer_instance

variable (j : Spec (.of B) ⟶ X) (hj : j ≫ β = Spec.algebraMap R B)
  (f : A →ₐ[R] B) (hf : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ i = j)

/-- Every original test projection commutes with coefficient refinement. -/
theorem sheafQuotientTestMap_refinement :
    (grassmannianAmbientSheafPullbackIso (M := M) f).inv ≫
      (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).map
        (sheafQuotientTestMap β p i hi) =
      sheafQuotientTestMap β p j hj ≫ (comparison _ i j hf).inv.app P := by
  have hw : Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.algebraMap R A =
      Spec.algebraMap R B := by rw [← hi, ← Category.assoc, hf, hj]
  have hc := grassmannianBaseAmbientComposes (M := M) f hw
  unfold sheafQuotientTestMap grassmannianSchemeAmbientTestIso grassmannianSchemeAmbient
  unfold grassmannianSchemeAmbient at p
  exact SheafPullbackAmbientTestRefinement.quotient_refinement _ i β j _ _ hf hi hj hw
    (tilde (ModuleCat.of R (R ⊗[R] M))) _ _ _ hc p

variable (N : Module.Grassmannian A (A ⊗[R] M) d)
  (a : grassmannianQuotientSheaf N ≅ (pullback i).obj P)
  (ha : grassmannianQuotientSheafMap N ≫ a.hom = sheafQuotientTestMap β p i hi)

/-- Refine an original quotient presentation without assuming any overlap relation. -/
@[irreducible] def sheafQuotientTestRefinementIso :
    grassmannianQuotientSheaf (Module.Grassmannian.map f N) ≅ (pullback j).obj P :=
  (grassmannianQuotientSheafPullbackIso f N).symm ≪≫
    (pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).mapIso a ≪≫
      (comparison _ i j hf).app P

include ha in
/-- Refining a local presentation retains every original global quotient coordinate. -/
@[reassoc] theorem sheafQuotientTestRefinementIso_projection :
    grassmannianQuotientSheafMap (Module.Grassmannian.map f N) ≫
      (sheafQuotientTestRefinementIso i j f hf N a).hom = sheafQuotientTestMap β p j hj := by
  have hq : grassmannianQuotientSheafMap (Module.Grassmannian.map f N) ≫
      (grassmannianQuotientSheafPullbackIso f N).inv = grassmannianRefinedQuotientMap f N := by
    apply (cancel_mono (grassmannianQuotientSheafPullbackIso f N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact (grassmannianRefinedQuotientMap_comparison f N).symm
  unfold sheafQuotientTestRefinementIso
  dsimp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [← Category.assoc, ← Category.assoc, hq]
  unfold grassmannianRefinedQuotientMap
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, ha, ← Category.assoc,
    sheafQuotientTestMap_refinement β p i hi j hj f hf]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

include ha hf hj in
/-- Two local quotient presentations force equality of full relations on any common test. -/
theorem sheafQuotientTest_commonRelation {D : Type u} [CommRing D] [Algebra R D]
    (k : Spec (.of D) ⟶ X) (hk : k ≫ β = Spec.algebraMap R D)
    (g : D →ₐ[R] B) (hg : Spec.map (CommRingCat.ofHom g.toRingHom) ≫ k = j)
    (N' : Module.Grassmannian D (D ⊗[R] M) d)
    (a' : grassmannianQuotientSheaf N' ≅ (pullback k).obj P)
    (ha' : grassmannianQuotientSheafMap N' ≫ a'.hom = sheafQuotientTestMap β p k hk) :
    Module.Grassmannian.map f N = Module.Grassmannian.map g N' := by
  let t := sheafQuotientTestRefinementIso i j f hf N a
  let t' := sheafQuotientTestRefinementIso k j g hg N' a'
  apply grassmannianPoint_eq_of_quotientSheafIso _ _ (t ≪≫ t'.symm)
  change grassmannianQuotientSheafMap _ ≫ t.hom ≫ t'.inv = _
  rw [← Category.assoc, sheafQuotientTestRefinementIso_projection β p i hi j hj f hf N a ha]
  apply (cancel_mono t'.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (sheafQuotientTestRefinementIso_projection β p k hk j hj g hg N' a' ha').symm

end FLT.Mazur.GrassmannianChart
