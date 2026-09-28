/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeOpen
public import FLT.Mazur.CechSheafHZero
public import Mathlib.Algebra.Homology.Augment

/-!
# The augmented free Cech complex

The formal Cech object is sent to coproducts of free abelian sheaves, and its
alternating face complex is augmented to the constant integer sheaf. The
coproduct coordinates below identify the differential with the signed deletion
of tuple entries. No covering hypothesis is needed for this construction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open scoped Simplicial
open FLT.Mazur.CechFreeOpen

universe u

namespace FLT.Mazur.CechFreeResolution

variable {X : TopCat.{u}} {ι : Type u}


/-- The free sheaf construction, functorially in the open. -/
def freeOpenFunctor : Opens X ⥤ (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- The constant integer sheaf which receives the augmentation. -/
abbrev integerSheaf : (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Every generator of a free representable is sent to the integer one. -/
def generatorToInteger (W : Opens X) : yoneda.obj W ⋙ AddCommGrpCat.free ⟶
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)) where
  app _ := AddCommGrpCat.ofHom (FreeAbelianGroup.lift fun _ ↦ ULift.up 1)
  naturality _ _ _ := by
    apply AddCommGrpCat.hom_ext
    apply FreeAbelianGroup.lift_ext
    intro x
    simp

lemma generatorToInteger_of (W T : Opens X) (f : T ⟶ W) :
    (generatorToInteger W).app (op T) (FreeAbelianGroup.of f) = ULift.up 1 := by
  simp [generatorToInteger]

/-- The augmentation on one free open sheaf. -/
def freeOpenAugmentation (W : Opens X) : freeOpen W ⟶ integerSheaf (X := X) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
    (generatorToInteger W)

@[reassoc (attr := simp)]
lemma freeOpenMap_augmentation {W T : Opens X} (f : W ⟶ T) :
    freeOpenMap f ≫ freeOpenAugmentation T = freeOpenAugmentation W := by
  rw [freeOpenMap, freeOpenAugmentation, ← Functor.map_comp]
  congr 1
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply FreeAbelianGroup.lift_ext
  intro x
  simp [generatorToInteger]

/-- The section corresponding to a generator after sheafification. -/
def freeOpenGenerator (W T : Opens X) (f : T ⟶ W) : (freeOpen W).obj.obj (op T) :=
  (toSheafify (Opens.grothendieckTopology X)
    (yoneda.obj W ⋙ AddCommGrpCat.free)).app (op T) (FreeAbelianGroup.of f)

/-- The constant section one, viewed in the sheafified constant presheaf. -/
def integerOne (T : Opens X) : (integerSheaf (X := X)).obj.obj (op T) :=
  (toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op T) (ULift.up 1)

/-- The sheaf augmentation sends every local generator to the constant section one. -/
lemma freeOpenAugmentation_generator (W T : Opens X) (f : T ⟶ W) :
    (freeOpenAugmentation W).hom.app (op T) (freeOpenGenerator W T f) = integerOne T := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology X)
      (generatorToInteger W)) (op T)) (FreeAbelianGroup.of f)
  change (toSheafify (Opens.grothendieckTopology X)
    ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app (op T)
      ((generatorToInteger W).app (op T) (FreeAbelianGroup.of f)) =
    (freeOpenAugmentation W).hom.app (op T) (freeOpenGenerator W T f) at h
  rw [generatorToInteger_of] at h
  exact h.symm

/-- Extend free sheaves to formal coproducts. -/
def freeCoproductFunctor : FormalCoproduct.{u} (Opens X) ⥤ (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (FormalCoproduct.eval _ _).obj freeOpenFunctor

/-- The augmentation of a formal coproduct of free opens. -/
def coproductAugmentation (A : FormalCoproduct.{u} (Opens X)) :
    (freeCoproductFunctor (X := X)).obj A ⟶ integerSheaf (X := X) :=
  Sigma.desc fun a ↦ freeOpenAugmentation (A.obj a)

@[reassoc (attr := simp)]
lemma freeCoproductFunctor_map_augmentation {A B : FormalCoproduct.{u} (Opens X)}
    (f : A ⟶ B) :
    (freeCoproductFunctor (X := X)).map f ≫ coproductAugmentation B = coproductAugmentation A := by
  apply Sigma.hom_ext
  intro a
  change Sigma.ι _ a ≫ (Sigma.desc _ ≫ Sigma.desc _) = _
  rw [Sigma.ι_comp_desc_assoc]
  change freeOpenMap (f.φ a) ≫
    (Sigma.ι (fun b ↦ freeOpen (B.obj b)) (f.f a) ≫
      Sigma.desc (fun b ↦ freeOpenAugmentation (B.obj b))) = _
  rw [Sigma.ι_comp_desc]
  dsimp only [coproductAugmentation]
  rw [Sigma.ι_comp_desc]
  exact freeOpenMap_augmentation (f.φ a)

variable (U : ι → Opens X)

/-- The simplicial free sheaves of the formal Cech object. -/
def freeSimplicial : SimplicialObject (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  (FormalCoproduct.mk ι U).cech ⋙ freeCoproductFunctor

/-- The unaugmented alternating face complex. -/
def freeComplex : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex
    (TopCat.Sheaf AddCommGrpCat.{u} X)).obj (freeSimplicial U)

/-- The augmentation is annihilated by the first alternating differential. -/
lemma freeComplex_d_augmentation :
    (freeComplex U).d 1 0 ≫
      coproductAugmentation ((FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)) = 0 := by
  dsimp only [freeComplex, AlgebraicTopology.alternatingFaceMapComplex]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  simp [Fin.sum_univ_two, freeSimplicial,
    SimplicialObject.δ, Functor.comp_map]

/-- The augmented free Cech complex, with the constant integers in degree zero. -/
def freeAugmented : ChainComplex (TopCat.Sheaf AddCommGrpCat.{u} X) ℕ :=
  (freeComplex U).augment
    (coproductAugmentation ((FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌)))
    (freeComplex_d_augmentation U)

/-- Degree zero is the constant integer sheaf. -/
def freeAugmentedZeroIso : (freeAugmented U).X 0 ≅ integerSheaf := Iso.refl _

/-- The intersection of the opens in an ordered tuple. -/
abbrev V (n : ℕ) (a : Fin (n + 1) → ι) : Opens X := ⨅ j, U (a j)

/-- Convert the categorical product open into its intersection description. -/
def productOpenIso (n : ℕ) (a : Fin (n + 1) → ι) : ∏ᶜ (U ∘ a) ≅ V U n a :=
  eqToIso (CechSheafHZero.productOpen_eq U n a)

/-- Positive degrees are coproducts of the free sheaves on intersections. -/
def freeAugmentedTermIso (n : ℕ) : (freeAugmented U).X (n + 1) ≅
    ∐ (fun a : Fin (n + 1) → ι ↦ freeOpen (V U n a)) :=
  Sigma.mapIso fun a ↦ freeOpenFunctor.mapIso (productOpenIso U n a)

/-- The summand inclusion in the augmented complex. -/
def freeAugmentedι (n : ℕ) (a : Fin (n + 1) → ι) :
    freeOpen (V U n a) ⟶ (freeAugmented U).X (n + 1) :=
  Sigma.ι (fun b : Fin (n + 1) → ι ↦ freeOpen (V U n b)) a ≫
    (freeAugmentedTermIso U n).inv

/-- Deleting one entry enlarges the intersection. -/
def faceInclusion (n : ℕ) (a : Fin (n + 2) → ι) (i : Fin (n + 2)) :
    V U (n + 1) a ⟶ V U n (a ∘ i.succAbove) :=
  homOfLE (le_iInf fun j ↦ iInf_le _ (i.succAbove j))

lemma freeAugmentedι_eq (n : ℕ) (a : Fin (n + 1) → ι) :
    freeAugmentedι U n a = freeOpenMap (productOpenIso U n a).inv ≫
      Sigma.ι (fun b : Fin (n + 1) → ι ↦ freeOpen (∏ᶜ (U ∘ b))) a := by
  change Sigma.ι _ a ≫ (Sigma.mapIso _).inv = _
  rw [Sigma.ι_mapIso_inv]
  rfl

/-- A face map on a summand deletes the corresponding tuple entry. -/
lemma freeAugmentedι_face (n : ℕ) (a : Fin (n + 2) → ι) (i : Fin (n + 2)) :
    freeAugmentedι U (n + 1) a ≫ (freeSimplicial U).δ i =
      freeOpenMap (faceInclusion U n a i) ≫ freeAugmentedι U n (a ∘ i.succAbove) := by
  simp only [freeAugmentedι_eq, Category.assoc]
  simp only [freeSimplicial, SimplicialObject.δ, Functor.comp_map,
    freeCoproductFunctor, FormalCoproduct.eval, FormalCoproduct.cech,
    FormalCoproduct.mapPower, Sigma.ι_comp_desc]
  change freeOpenFunctor.map _ ≫ (freeOpenFunctor.map _ ≫ _) =
    freeOpenFunctor.map _ ≫ (freeOpenFunctor.map _ ≫ _)
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2

/-- The differential is the alternating sum of deletion maps on each summand. -/
lemma freeAugmentedι_d (n : ℕ) (a : Fin (n + 2) → ι) :
    freeAugmentedι U (n + 1) a ≫ (freeAugmented U).d (n + 2) (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        (freeOpenMap (faceInclusion U n a i) ≫ freeAugmentedι U n (a ∘ i.succAbove)) := by
  change freeAugmentedι U (n + 1) a ≫ (freeComplex U).d (n + 1) n = _
  dsimp only [freeComplex, AlgebraicTopology.alternatingFaceMapComplex]
  rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Preadditive.comp_sum]
  simp only [Preadditive.comp_zsmul, freeAugmentedι_face]

/-- Each degree-one summand is augmented by sending its generator to one. -/
@[reassoc]
lemma freeAugmentedι_augmentation (a : Fin 1 → ι) :
    freeAugmentedι U 0 a ≫ (freeAugmented U).d 1 0 ≫
      (freeAugmentedZeroIso U).hom = freeOpenAugmentation (V U 0 a) := by
  rw [freeAugmentedι_eq]
  change (_ ≫ Sigma.ι _ a) ≫ Sigma.desc _ ≫ 𝟙 _ = _
  rw [Category.comp_id, Category.assoc, Sigma.ι_comp_desc]
  exact freeOpenMap_augmentation _

end FLT.Mazur.CechFreeResolution
