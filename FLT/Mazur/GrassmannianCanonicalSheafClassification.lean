/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientClassification

/-!
# Canonical classification and isomorphisms of original sheaf quotients

The atlas predicate retains each full original projection. Existence is
constructed from local frames, and uniqueness compares arbitrary source covers.
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
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
  {P : X.Modules} (p : grassmannianSchemeAmbient (M := M) β ⟶ P)
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)
attribute [local irreducible] Scheme.Modules.pullback grassmannianQuotientSheaf

/-- A quotient isomorphism preserves classification, including the entire ambient map. -/
theorem SheafQuotientClassifies.of_iso
    {Q : X.Modules} (q : grassmannianSchemeAmbient (M := M) β ⟶ Q)
    (e : P ≅ Q) (he : p ≫ e.hom = q)
    {f : X ⟶ ambientGrassmannianScheme R M κ d}
    (h : SheafQuotientClassifies β p b hκ f) :
    SheafQuotientClassifies β q b hκ f := by
  unfold SheafQuotientClassifies at h ⊢
  obtain ⟨C, a, hC, N, hf, ht⟩ := h
  let _ := a
  refine ⟨C, a, hC, N, hf, ?_⟩
  intro j
  obtain ⟨t, ht⟩ := ht j
  refine ⟨t ≪≫ (pullback (C.f j)).mapIso e, ?_⟩
  change grassmannianQuotientSheafMap _ ≫ t.hom ≫ (pullback (C.f j)).map e.hom = _
  rw [← Category.assoc, ht]
  unfold sheafQuotientTestMap
  rw [Category.assoc, ← Functor.map_comp, he]

variable [Epi p] {τ : Type u} [Fintype τ]
  (hP : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (P.restrict U.ι ≅ SheafOfModules.free τ)) (hd : Fintype.card τ = d)

/-- The scheme morphism constructed from only the original epimorphism and local frames. -/
@[irreducible] def locallyFreeQuotientClassifyingMap :
    X ⟶ ambientGrassmannianScheme R M κ d :=
  (existsUnique_sheafQuotientClassifies β p b hκ hP hd).exists.choose

/-- The chosen classifying map has a constructed original quotient atlas. -/
theorem locallyFreeQuotientClassifyingMap_spec :
    SheafQuotientClassifies β p b hκ
      (locallyFreeQuotientClassifyingMap β p b hκ hP hd) := by
  unfold locallyFreeQuotientClassifyingMap
  exact (existsUnique_sheafQuotientClassifies β p b hκ hP hd).exists.choose_spec

/-- The chosen map preserves the original base scheme morphism. -/
@[reassoc] theorem locallyFreeQuotientClassifyingMap_over :
    locallyFreeQuotientClassifyingMap β p b hκ hP hd ≫
      ambientGrassmannianStructure R M κ d = β :=
  (locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd).over β p b hκ

/-- Neither the selected local frames nor their finite index type affect classification. -/
theorem locallyFreeQuotientClassifyingMap_frameIndependent {σ : Type u} [Fintype σ]
    (hP' : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (P.restrict U.ι ≅ SheafOfModules.free σ)) (hd' : Fintype.card σ = d) :
    locallyFreeQuotientClassifyingMap β p b hκ hP hd =
      locallyFreeQuotientClassifyingMap β p b hκ hP' hd' :=
  (locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd).unique β p b hκ
    (locallyFreeQuotientClassifyingMap_spec β p b hκ hP' hd')

/-- Isomorphic full quotients give the same actual classifying scheme morphism. -/
theorem locallyFreeQuotientClassifyingMap_iso {σ : Type u} [Fintype σ]
    {Q : X.Modules} (q : grassmannianSchemeAmbient (M := M) β ⟶ Q) [Epi q]
    (hQ : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (Q.restrict U.ι ≅ SheafOfModules.free σ)) (hd' : Fintype.card σ = d)
    (e : P ≅ Q) (he : p ≫ e.hom = q) :
    locallyFreeQuotientClassifyingMap β p b hκ hP hd =
      locallyFreeQuotientClassifyingMap β q b hκ hQ hd' :=
  ((locallyFreeQuotientClassifyingMap_spec β p b hκ hP hd).of_iso β p b hκ q e he).unique
    β q b hκ (locallyFreeQuotientClassifyingMap_spec β q b hκ hQ hd')

end FLT.Mazur.GrassmannianChart
