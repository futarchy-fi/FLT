/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeStalkInsertion

/-!
# Exactness of the augmented free Cech complex on stalks

The augmented alternating complex of free Cech stalks agrees with the stalk of
the augmented free complex, including its integer term. Insertion of a cover
member containing the point proves exactness in every degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open AlgebraicTopology
open scoped Simplicial

universe u

namespace FLT.Mazur.CechFreeResolution

variable {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X)

/-- Taking stalks commutes with the alternating differential. -/
lemma freeStalkComplex_d (x : X) (n : ℕ) :
    (AlternatingFaceMapComplex.obj (freeStalkAugmented U x).left).d (n + 1) n =
      (sheafStalk x).map ((freeComplex U).d (n + 1) n) := by
  change _ = (sheafStalk x).map
    ((AlternatingFaceMapComplex.obj (freeSimplicial U)).d (n + 1) n)
  simp only [AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum, Functor.map_zsmul]
  rfl

/-- The stalk augmentation annihilates the first alternating differential. -/
lemma freeStalkComplex_d_augmentation (x : X) :
    (AlternatingFaceMapComplex.obj (freeStalkAugmented U x).left).d 1 0 ≫
      (freeStalkAugmented U x).hom.app (op ⦋0⦌) = 0 := by
  rw [freeStalkComplex_d]
  change (sheafStalk x).map ((freeComplex U).d 1 0) ≫
    (sheafStalk x).map (coproductAugmentation
      ((FormalCoproduct.mk ι U).cech.obj (op ⦋0⦌))) = 0
  rw [← Functor.map_comp, freeComplex_d_augmentation, Functor.map_zero]

/-- The augmented alternating complex formed after taking stalks. -/
def freeStalkAugmentedComplex (x : X) : ChainComplex AddCommGrpCat.{u} ℕ :=
  (AlternatingFaceMapComplex.obj (freeStalkAugmented U x).left).augment
    ((freeStalkAugmented U x).hom.app (op ⦋0⦌)) (freeStalkComplex_d_augmentation U x)

/-- The comparison includes the integer term as well as every positive term. -/
def freeStalkAugmentedComplexIso (x : X) : freeStalkAugmentedComplex U x ≅
    ((sheafStalk x).mapHomologicalComplex (ComplexShape.down ℕ)).obj (freeAugmented U) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun | 0 => Iso.refl _ | _ + 1 => Iso.refl _)
    (by
      intro i j hij
      obtain rfl : j + 1 = i := hij
      cases j with
      | zero => simp [freeStalkAugmentedComplex, freeAugmented, freeStalkAugmented]
      | succ n =>
        change 𝟙 _ ≫ (sheafStalk x).map ((freeComplex U).d (n + 1) n) =
          (AlternatingFaceMapComplex.obj (freeStalkAugmented U x).left).d (n + 1) n ≫ 𝟙 _
        simpa only [Category.id_comp, Category.comp_id] using (freeStalkComplex_d U x n).symm)

/-- Every stalk of the augmented free complex of an open cover is exact in every degree. -/
lemma freeAugmented_stalk_exactAt (hU : iSup U = ⊤) (x : X) (n : ℕ) :
    (((sheafStalk x).mapHomologicalComplex (ComplexShape.down ℕ)).obj
      (freeAugmented U)).ExactAt n := by
  obtain ⟨i, hi⟩ := exists_coverIndex U hU x
  exact (extraDegeneracy_augmented_exactAt (freeStalkAugmented U x)
    (freeStalkExtraDegeneracy U x i hi) (freeStalkComplex_d_augmentation U x) n).of_iso
      (freeStalkAugmentedComplexIso U x)

end FLT.Mazur.CechFreeResolution
