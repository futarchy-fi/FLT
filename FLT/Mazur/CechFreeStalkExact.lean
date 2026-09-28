/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeOpenStalk
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.AlgebraicTopology.ExtraDegeneracy

/-!
# Exactness tools for the stalks of the augmented free Cech complex

An extra degeneracy gives exactness of the augmented alternating complex,
including its degree zero. The augmentation of the free Cech complex is
surjective on stalks for an open cover.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open TopCat.Presheaf AlgebraicTopology
open scoped Simplicial

universe u

namespace FLT.Mazur.CechFreeResolution

/-- The bottom contraction identity includes the augmentation term. -/
lemma extraDegeneracy_contraction_zero (A : SimplicialObject.Augmented AddCommGrpCat.{u})
    (ed : A.ExtraDegeneracy) :
    (ed.s 0 ≫ (AlternatingFaceMapComplex.obj A.left).d 1 0 :
      A.left _⦋0⦌ ⟶ A.left _⦋0⦌) +
      (A.hom.app (op ⦋0⦌) ≫ ed.s' : A.left _⦋0⦌ ⟶ A.left _⦋0⦌) = 𝟙 _ := by
  simp [AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two,
    ed.s₀_comp_δ₁]

/-- In higher degrees the two adjacent contraction terms add to the identity. -/
lemma extraDegeneracy_contraction_succ (A : SimplicialObject.Augmented AddCommGrpCat.{u})
    (ed : A.ExtraDegeneracy) (n : ℕ) :
    (ed.s (n + 1) ≫ (AlternatingFaceMapComplex.obj A.left).d (n + 2) (n + 1) :
      A.left _⦋n + 1⦌ ⟶ A.left _⦋n + 1⦌) +
      ((AlternatingFaceMapComplex.obj A.left).d (n + 1) n ≫ ed.s n :
        A.left _⦋n + 1⦌ ⟶ A.left _⦋n + 1⦌) = 𝟙 _ := by
  rw [AlternatingFaceMapComplex.obj_d_eq, AlternatingFaceMapComplex.obj_d_eq,
    Fin.sum_univ_succ]
  simp only [Preadditive.comp_add, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp, Fin.val_zero, Fin.val_succ,
    pow_zero, one_zsmul, ed.s_comp_δ₀, ed.s_comp_δ, pow_succ, mul_neg_one,
    neg_zsmul, Finset.sum_neg_distrib, Preadditive.comp_neg]
  abel

/-- Extra degeneracies make the augmented alternating complex exact in every degree. -/
lemma extraDegeneracy_augmented_exactAt (A : SimplicialObject.Augmented AddCommGrpCat.{u})
    (ed : A.ExtraDegeneracy)
    (w : (AlternatingFaceMapComplex.obj A.left).d 1 0 ≫ A.hom.app (op ⦋0⦌) = 0)
    (n : ℕ) :
    ((AlternatingFaceMapComplex.obj A.left).augment (A.hom.app (op ⦋0⦌)) w).ExactAt n := by
  cases n with
  | zero =>
    rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    intro z _
    exact ⟨ed.s' z, ConcreteCategory.congr_hom ed.s'_comp_ε z⟩
  | succ n =>
    rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
      ShortComplex.ab_exact_iff]
    change ∀ (z : A.left _⦋n⦌), _
    intro z hz
    refine ⟨ed.s n z, ?_⟩
    cases n with
    | zero =>
      have h := ConcreteCategory.congr_hom (extraDegeneracy_contraction_zero A ed) z
      change A.hom.app (op ⦋0⦌) z = 0 at hz
      have hzero : (A.hom.app (op ⦋0⦌) ≫ ed.s') z = 0 := by
        change ed.s' (A.hom.app (op ⦋0⦌) z) = 0
        rw [hz, map_zero]
      rw [AddCommGrpCat.hom_add_apply] at h
      erw [hzero, add_zero] at h
      exact h
    | succ n =>
      have h := ConcreteCategory.congr_hom (extraDegeneracy_contraction_succ A ed n) z
      change (AlternatingFaceMapComplex.obj A.left).d (n + 1) n z = 0 at hz
      have hzero : ((AlternatingFaceMapComplex.obj A.left).d (n + 1) n ≫ ed.s n) z = 0 := by
        change ed.s n ((AlternatingFaceMapComplex.obj A.left).d (n + 1) n z) = 0
        rw [hz, map_zero]
      rw [AddCommGrpCat.hom_add_apply] at h
      erw [hzero, add_zero] at h
      exact h

open FLT.Mazur.CechFreeOpen

variable {X : TopCat.{u}}

/-- The free abelian sheaf on the whole space is the constant integer sheaf. -/
instance freeOpenAugmentation_top_isIso :
    IsIso (freeOpenAugmentation (⊤ : Opens X)) := by
  have : ∀ T, IsIso ((generatorToInteger (⊤ : Opens X)).app T) := by
    intro T
    let : Unique (T.unop ⟶ (⊤ : Opens X)) :=
      ⟨⟨homOfLE le_top⟩, fun _ ↦ Subsingleton.elim _ _⟩
    let e : AddCommGrpCat.of (FreeAbelianGroup (T.unop ⟶ (⊤ : Opens X))) ≅
        AddCommGrpCat.of (ULift.{u} ℤ) :=
      ((FreeAbelianGroup.uniqueEquiv (T.unop ⟶ (⊤ : Opens X))).trans
        AddEquiv.ulift.symm).toAddCommGrpIso
    have h : (generatorToInteger (⊤ : Opens X)).app T = e.hom := by
      apply AddCommGrpCat.hom_ext
      apply FreeAbelianGroup.lift_ext
      intro f
      simp [generatorToInteger, e, FreeAbelianGroup.uniqueEquiv, AddEquiv.ulift]
    rw [h]
    infer_instance
  have : IsIso (generatorToInteger (⊤ : Opens X)) := NatIso.isIso_of_isIso_app _
  exact Functor.map_isIso _ _

/-- An inclusion between neighborhoods induces an isomorphism on free-open stalks. -/
lemma freeOpenMap_stalk_isIso {W T : Opens X} (i : W ⟶ T) (x : X) (hx : x ∈ W) :
    IsIso ((sheafStalk x).map (freeOpenMap i)) := by
  let e : OpenFiber W x ≃ OpenFiber T x :=
    { toFun := openFiberMap i x
      invFun := fun _ ↦ ⟨⟨hx⟩⟩
      left_inv := fun _ ↦ Subsingleton.elim _ _
      right_inv := fun _ ↦ Subsingleton.elim _ _ }
  have he : freeOpenStalkMap i x = (Finsupp.domCongr e).toAddCommGrpIso.hom := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    exact (Finsupp.equivMapDomain_eq_mapDomain e z).symm
  have : IsIso (freeOpenStalkMap i x) := by rw [he]; infer_instance
  have h := freeOpenStalkIso_naturality i x
  change (sheafStalk x).map (freeOpenMap i) ≫ _ = _ at h
  have : IsIso ((sheafStalk x).map (freeOpenMap i) ≫ (freeOpenStalkIso T x).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (freeOpenStalkIso T x).hom

/-- At a point of the open, its free augmentation is an isomorphism on stalks. -/
lemma freeOpenAugmentation_stalk_isIso (W : Opens X) (x : X) (hx : x ∈ W) :
    IsIso ((sheafStalk x).map (freeOpenAugmentation W)) := by
  let i : W ⟶ (⊤ : Opens X) := homOfLE le_top
  have := freeOpenMap_stalk_isIso i x hx
  rw [← freeOpenMap_augmentation i, Functor.map_comp]
  infer_instance

variable {ι : Type u} (U : ι → Opens X)

/-- A covering family contains a neighborhood of every point. -/
lemma exists_coverIndex (hU : iSup U = ⊤) (x : X) : ∃ i, x ∈ U i := by
  have hx : x ∈ iSup U := by rw [hU]; trivial
  simpa only [Opens.mem_iSup] using hx

/-- The augmentation on stalks has a section obtained from a covering member. -/
def freeAugmentedStalkSection (x : X) (i : ι) (hi : x ∈ U i) :
    (sheafStalk x).obj ((freeAugmented U).X 0) ⟶
      (sheafStalk x).obj ((freeAugmented U).X 1) := by
  let a : Fin 1 → ι := fun _ ↦ i
  have hx : x ∈ V U 0 a := by simpa [V, a] using hi
  have := freeOpenAugmentation_stalk_isIso (V U 0 a) x hx
  exact (sheafStalk x).map (freeAugmentedZeroIso U).hom ≫
    inv ((sheafStalk x).map (freeOpenAugmentation (V U 0 a))) ≫
      (sheafStalk x).map (freeAugmentedι U 0 a)

/-- The chosen stalk section is a right inverse to the augmented differential. -/
@[reassoc]
lemma freeAugmentedStalkSection_d (x : X) (i : ι) (hi : x ∈ U i) :
    freeAugmentedStalkSection U x i hi ≫
      (sheafStalk x).map ((freeAugmented U).d 1 0) = 𝟙 _ := by
  let a : Fin 1 → ι := fun _ ↦ i
  have hx : x ∈ V U 0 a := by simpa [V, a] using hi
  have := freeOpenAugmentation_stalk_isIso (V U 0 a) x hx
  apply (cancel_mono ((sheafStalk x).map (freeAugmentedZeroIso U).hom)).mp
  dsimp only [freeAugmentedStalkSection]
  simp only [Category.assoc, ← Functor.map_comp, freeAugmentedι_augmentation]
  simp

/-- The degree-zero term is exact on stalks, including the integer augmentation. -/
lemma freeAugmented_stalk_exactAt_zero (hU : iSup U = ⊤) (x : X) :
    (((sheafStalk x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (freeAugmented U)).ExactAt 0 := by
  obtain ⟨i, hi⟩ := exists_coverIndex U hU x
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp),
    ShortComplex.ab_exact_iff]
  intro z _
  exact ⟨freeAugmentedStalkSection U x i hi z,
    ConcreteCategory.congr_hom (freeAugmentedStalkSection_d U x i hi) z⟩

end FLT.Mazur.CechFreeResolution
