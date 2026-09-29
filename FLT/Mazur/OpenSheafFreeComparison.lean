/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeOpen
public import FLT.Mazur.OpenSheafRestriction
public import Mathlib.CategoryTheory.Limits.Lattice

/-!
# Extension of the constant integer sheaf

Maps from the extension of the constant integer sheaf represent sections on
the ambient open. This equivalence is natural in the coefficient sheaf, and
identifies the extension with the free abelian sheaf on that open.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open FLT.Mazur.OpenSheafRestriction FLT.Mazur.CechFreeOpen

universe u

namespace FLT.Mazur.OpenSheafFreeComparison

/-- The constant integer sheaf, using integers in the space's universe. -/
abbrev constantInteger (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X :=
  (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))

/-- Maps from the constant integer sheaf are global sections. -/
def constantIntegerHomEquiv {X : TopCat.{u}} (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (constantInteger X ⟶ F) ≃+ F.obj.obj (op ⊤) :=
  ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    (isTerminalTop (α := Opens X))).homAddEquiv _ F).trans
      (AddCommGrpCat.uliftZMultiplesAddEquiv _)

/-- Global-section evaluation is natural in the coefficient sheaf. -/
lemma constantIntegerHomEquiv_naturality {X : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (g : constantInteger X ⟶ F) :
    constantIntegerHomEquiv G (g ≫ f) =
      f.hom.app (op ⊤) (constantIntegerHomEquiv F g) := by
  change AddCommGrpCat.uliftZMultiplesAddEquiv _
    ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
      (isTerminalTop (α := Opens X))).homEquiv _ G (g ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

variable {X : TopCat.{u}} (W : Opens X)

/-- The top-open restriction comparison commutes with coefficient morphisms. -/
lemma restrictionTopIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (s : ((restriction W).obj F).obj.obj (op ⊤)) :
    (restrictionTopIso W G).hom (((restriction W).map f).hom.app (op ⊤) s) =
      f.hom.app (op W) ((restrictionTopIso W F).hom s) := by
  exact (ConcreteCategory.congr_hom (f.hom.naturality _) s).symm

/-- The extension of the constant integer sheaf represents sections on the open. -/
def extensionIntegerHomEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((extension W).obj (constantInteger (TopCat.of W)) ⟶ F) ≃ F.obj.obj (op W) :=
  ((homEquiv W (constantInteger (TopCat.of W)) F).trans
    (constantIntegerHomEquiv ((restriction W).obj F)).toEquiv).trans
      (restrictionTopIso W F).addCommGroupIsoToAddEquiv.toEquiv

/-- Section representation by the extension is natural in the coefficient sheaf. -/
lemma extensionIntegerHomEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (g : (extension W).obj (constantInteger (TopCat.of W)) ⟶ F) :
    extensionIntegerHomEquiv W G (g ≫ f) =
      f.hom.app (op W) (extensionIntegerHomEquiv W F g) := by
  change (restrictionTopIso W G).hom
    (constantIntegerHomEquiv _ ((adjunction W).homEquiv _ G (g ≫ f))) = _
  rw [Adjunction.homEquiv_naturality_right, constantIntegerHomEquiv_naturality]
  exact restrictionTopIso_naturality W f _

/-- Both objects have the same natural section-representing Hom functor. -/
def homComparison (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((extension W).obj (constantInteger (TopCat.of W)) ⟶ F) ≃ (freeOpen W ⟶ F) :=
  (extensionIntegerHomEquiv W F).trans (freeOpenHomEquiv W F).toEquiv.symm

/-- The Hom comparison preserves the represented section. -/
lemma homComparison_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (g : (extension W).obj (constantInteger (TopCat.of W)) ⟶ F) :
    freeOpenHomEquiv W F (homComparison W F g) = extensionIntegerHomEquiv W F g :=
  (freeOpenHomEquiv W F).apply_symm_apply _

/-- The Hom comparison commutes with postcomposition. -/
lemma homComparison_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (g : (extension W).obj (constantInteger (TopCat.of W)) ⟶ F) :
    homComparison W G (g ≫ f) = homComparison W F g ≫ f := by
  apply (freeOpenHomEquiv W G).injective
  rw [homComparison_evaluation, freeOpenHomEquiv_naturality,
    homComparison_evaluation, extensionIntegerHomEquiv_naturality]

/-- Extension of the constant integer sheaf is the ambient free-open sheaf. -/
def extensionFreeOpenIso :
    (extension W).obj (constantInteger (TopCat.of W)) ≅ freeOpen W where
  hom := (homComparison W (freeOpen W)).symm (𝟙 _)
  inv := homComparison W _ (𝟙 _)
  hom_inv_id := by
    apply (homComparison W _).injective
    rw [homComparison_naturality]
    simp only [Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := homComparison_naturality W
      ((homComparison W (freeOpen W)).symm (𝟙 _)) (𝟙 _)
    simpa only [Category.id_comp, Equiv.apply_symm_apply] using h.symm

/-- Precomposition with the comparison gives exactly the section-representing equivalence. -/
lemma extensionFreeOpenIso_hom_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (g : freeOpen W ⟶ F) :
    extensionIntegerHomEquiv W F ((extensionFreeOpenIso W).hom ≫ g) =
      freeOpenHomEquiv W F g := by
  rw [← homComparison_evaluation, homComparison_naturality]
  change freeOpenHomEquiv W F
    ((homComparison W (freeOpen W)) ((homComparison W (freeOpen W)).symm (𝟙 _)) ≫ g) = _
  simp only [Equiv.apply_symm_apply, Category.id_comp]

/-- The inverse comparison likewise preserves the represented section. -/
lemma extensionFreeOpenIso_inv_evaluation (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (g : (extension W).obj (constantInteger (TopCat.of W)) ⟶ F) :
    freeOpenHomEquiv W F ((extensionFreeOpenIso W).inv ≫ g) =
      extensionIntegerHomEquiv W F g := by
  rw [← extensionFreeOpenIso_hom_evaluation]
  simp only [Iso.hom_inv_id_assoc]

end FLT.Mazur.OpenSheafFreeComparison
