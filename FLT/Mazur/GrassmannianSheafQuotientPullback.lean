/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientTest

/-!
# Arbitrary scheme pullback of the full original ambient quotient

The base ambient comparison normalizes the pulled-back epimorphism. Its affine
tests retain the complete original projection and the actual composite scheme path.
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
variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
variable {X Y : Scheme.{u}} (β : X ⟶ Spec (.of R)) (g : Y ⟶ X)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- Actual arbitrary-source pullback of the original base ambient sheaf. -/
@[irreducible] def grassmannianSchemeAmbientPullbackIso :
    (pullback g).obj (grassmannianSchemeAmbient (M := M) β) ≅
      grassmannianSchemeAmbient (M := M) (g ≫ β) := by
  unfold grassmannianSchemeAmbient
  exact (comparison g β (g ≫ β) rfl).app _

variable {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)

/-- Pull back the entire quotient projection along an arbitrary scheme morphism. -/
@[irreducible] def sheafQuotientPullbackMap :
    grassmannianSchemeAmbient (M := M) (g ≫ β) ⟶ (pullback g).obj P :=
  (grassmannianSchemeAmbientPullbackIso β g).inv ≫ (pullback g).map p

/-- Arbitrary pullback of an original ambient epimorphism is still an epimorphism. -/
instance sheafQuotientPullbackMap_epi [Epi p] : Epi (sheafQuotientPullbackMap β g p) := by
  unfold sheafQuotientPullbackMap
  infer_instance

/-- Every affine test of the pulled-back quotient is its original composite test. -/
theorem sheafQuotientPullbackMap_test {A : Type u} [CommRing A] [Algebra R A]
    (z : Spec (.of A) ⟶ Y) (hz : z ≫ (g ≫ β) = Spec.algebraMap R A) :
    sheafQuotientTestMap (g ≫ β) (sheafQuotientPullbackMap β g p) z hz =
      sheafQuotientTestMap β p (z ≫ g) ((Category.assoc z g β).trans hz) ≫
        (comparison z g (z ≫ g) rfl).inv.app P := by
  let L : (Spec (.of R)).Modules := tilde (ModuleCat.of R (R ⊗[R] M))
  let K : (Spec (.of A)).Modules := tilde (ModuleCat.of A (A ⊗[R] M))
  let c := grassmannianAmbientSheafPullbackIso (M := M) (Algebra.ofId R A)
  let e := testIso (z ≫ g) β (Spec.algebraMap R A)
    ((Category.assoc z g β).trans hz) L K c
  have hc : e.inv ≫ (pullback (z ≫ g)).map (Iso.refl ((pullback β).obj L)).inv ≫
      (comparison (z ≫ g) β (Spec.algebraMap R A)
        ((Category.assoc z g β).trans hz)).hom.app L = c.inv := by
    simp only [e, testIso, Iso.trans_inv, Iso.app_inv, Iso.refl_inv, (pullback (z ≫ g)).map_id,
      Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  unfold sheafQuotientTestMap sheafQuotientPullbackMap
    grassmannianSchemeAmbientTestIso grassmannianSchemeAmbientPullbackIso
  unfold grassmannianSchemeAmbient at p ⊢
  have h := quotientMap_test z g β (g ≫ β) (z ≫ g) (Spec.algebraMap R A)
    rfl rfl hz ((Category.assoc z g β).trans hz) L ((pullback β).obj L) K
    (Iso.refl _) c e P p hc
  simpa only [chartIso, e, id, Iso.refl_symm,
    Functor.mapIso_refl, Iso.refl_trans, Category.assoc] using h

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (i : Spec (.of A) ⟶ X) (hi : i ≫ β = Spec.algebraMap R A)
  (z : Spec (.of B) ⟶ Y) (hz : z ≫ (g ≫ β) = Spec.algebraMap R B)
  (s : A →ₐ[R] B) (hs : Spec.map (CommRingCat.ofHom s.toRingHom) ≫ i = z ≫ g)
  {d : ℕ} (N : Module.Grassmannian A (A ⊗[R] M) d)
  (e : grassmannianQuotientSheaf N ≅ (pullback i).obj P)

/-- Pulling an original presentation back retains its actual refined quotient sheaf. -/
@[irreducible] def sheafQuotientPullbackTestIso :
    grassmannianQuotientSheaf (Module.Grassmannian.map s N) ≅
      (pullback z).obj ((pullback g).obj P) :=
  sheafQuotientTestRefinementIso i (z ≫ g) s hs N e ≪≫
    (comparison z g (z ≫ g) rfl).symm.app P

/-- The pulled-back local presentation retains every original ambient coordinate. -/
theorem sheafQuotientPullbackTestIso_projection
    (he : grassmannianQuotientSheafMap N ≫ e.hom = sheafQuotientTestMap β p i hi) :
    grassmannianQuotientSheafMap (Module.Grassmannian.map s N) ≫
        (sheafQuotientPullbackTestIso g i z s hs N e).hom =
      sheafQuotientTestMap (g ≫ β) (sheafQuotientPullbackMap β g p) z hz := by
  unfold sheafQuotientPullbackTestIso
  dsimp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [← Category.assoc, sheafQuotientTestRefinementIso_projection β p i hi (z ≫ g)
    ((Category.assoc z g β).trans hz) s hs N e he]
  exact (sheafQuotientPullbackMap_test β g p z hz).symm

end FLT.Mazur.GrassmannianChart
