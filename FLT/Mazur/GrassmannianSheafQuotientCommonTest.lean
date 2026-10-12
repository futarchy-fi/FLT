/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientTest
public import FLT.Mazur.GrassmannianAmbientClassifyingInjective

/-!
# Comparing original quotients on common affine tests

Equality of the actual classifying maps identifies every original relation
on a common coefficient algebra and constructs a full quotient comparison.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P Q : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
  (q : grassmannianSchemeAmbient (M := M) β ⟶ Q)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- Equal full affine relations yield a comparison preserving the entire test projection. -/
theorem exists_sheafQuotientTestIso {T : Type u} [CommRing T] [Algebra R T]
    (v : Spec (.of T) ⟶ X) (hv : v ≫ β = Spec.algebraMap R T)
    (N N' : Module.Grassmannian T (T ⊗[R] M) d) (hn : N = N')
    (e : grassmannianQuotientSheaf N ≅ (pullback v).obj P)
    (e' : grassmannianQuotientSheaf N' ≅ (pullback v).obj Q)
    (he : grassmannianQuotientSheafMap N ≫ e.hom = sheafQuotientTestMap β p v hv)
    (he' : grassmannianQuotientSheafMap N' ≫ e'.hom = sheafQuotientTestMap β q v hv) :
    ∃ t : (pullback v).obj P ≅ (pullback v).obj Q,
      (pullback v).map p ≫ t.hom = (pullback v).map q := by
  subst N'
  refine ⟨e.symm ≪≫ e', ?_⟩
  apply (cancel_epi (grassmannianSchemeAmbientTestIso (M := M) β v hv).inv).mp
  unfold sheafQuotientTestMap at he he'
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  rw [← he]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact he'

/-- Coincident classifying maps compare the full original quotients on a common affine test. -/
theorem exists_sheafQuotientCommonTestIso
    {A B T : Type u} [CommRing A] [CommRing B] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R T]
    (i : Spec (.of A) ⟶ X) (hi : i ≫ β = Spec.algebraMap R A)
    (k : Spec (.of B) ⟶ X) (hk : k ≫ β = Spec.algebraMap R B)
    (v : Spec (.of T) ⟶ X) (hv : v ≫ β = Spec.algebraMap R T)
    (l : A →ₐ[R] T) (hl : Spec.map (CommRingCat.ofHom l.toRingHom) ≫ i = v)
    (r : B →ₐ[R] T) (hr : Spec.map (CommRingCat.ofHom r.toRingHom) ≫ k = v)
    (N : Module.Grassmannian A (A ⊗[R] M) d)
    (N' : Module.Grassmannian B (B ⊗[R] M) d)
    (e : grassmannianQuotientSheaf N ≅ (pullback i).obj P)
    (e' : grassmannianQuotientSheaf N' ≅ (pullback k).obj Q)
    (he : grassmannianQuotientSheafMap N ≫ e.hom = sheafQuotientTestMap β p i hi)
    (he' : grassmannianQuotientSheafMap N' ≫ e'.hom = sheafQuotientTestMap β q k hk)
    (f : X ⟶ ambientGrassmannianScheme R M κ d)
    (hf : i ≫ f = ambientClassifyingMap b N hκ)
    (hf' : k ≫ f = ambientClassifyingMap b N' hκ) :
    ∃ t : (pullback v).obj P ≅ (pullback v).obj Q,
      (pullback v).map p ≫ t.hom = (pullback v).map q := by
  have hn : Module.Grassmannian.map l N = Module.Grassmannian.map r N' := by
    apply ambientClassifyingMap_injective b hκ
    dsimp only
    rw [ambientClassifyingMap_natural (B := T), ambientClassifyingMap_natural (B := T),
      ← hf, ← hf', ← Category.assoc, ← Category.assoc, hl, hr]
  exact exists_sheafQuotientTestIso β p q v hv _ _ hn
    (sheafQuotientTestRefinementIso i v l hl N e)
    (sheafQuotientTestRefinementIso k v r hr N' e')
    (sheafQuotientTestRefinementIso_projection β p i hi v hv l hl N e he)
    (sheafQuotientTestRefinementIso_projection β q k hk v hv r hr N' e' he')

end FLT.Mazur.GrassmannianChart
