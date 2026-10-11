/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Transport of overlap rotations by a pullback-preserving functor

Projection equations and cyclic identities survive the canonical pullback
comparisons. These abstract lemmas keep geometric reductions out of the proofs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)

/-- A cycle of three arrows stays a cycle after functorial transport and change of objects. -/
theorem functorConjugate_cocycle {A B E : C} {A' B' E' : D}
    (ea : A' ≅ F.obj A) (eb : B' ≅ F.obj B) (ee : E' ≅ F.obj E)
    (r : A ⟶ B) (s : B ⟶ E) (t : E ⟶ A) (h : r ≫ s ≫ t = 𝟙 _) :
    (ea.hom ≫ F.map r ≫ eb.inv) ≫ (eb.hom ≫ F.map s ≫ ee.inv) ≫
      (ee.hom ≫ F.map t ≫ ea.inv) = 𝟙 _ := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc,
    h, F.map_id, Category.id_comp, Iso.hom_inv_id]

variable {A B E P Q T : C} (l : A ⟶ E) (m : B ⟶ E) (n : P ⟶ T) (p : Q ⟶ T)
  [HasPullback l m] [HasPullback n p]
  [HasPullback (F.map l) (F.map m)] [HasPullback (F.map n) (F.map p)]
  [PreservesLimit (cospan l m) F] [PreservesLimit (cospan n p) F]

/-- The original rotation expressed between the actual target-category pullbacks. -/
def mappedPullbackRotation (r : pullback l m ⟶ pullback n p) :
    pullback (F.map l) (F.map m) ⟶ pullback (F.map n) (F.map p) :=
  (PreservesPullback.iso F l m).inv ≫ F.map r ≫ (PreservesPullback.iso F n p).hom

/-- The transported rotation preserves its second-projection equation. -/
theorem mappedPullbackRotation_snd (r : pullback l m ⟶ pullback n p) (t : A ⟶ Q)
    (h : r ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t) :
    mappedPullbackRotation F l m n p r ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ F.map t := by
  simpa [mappedPullbackRotation, Iso.inv_comp_eq] using congrArg F.map h

end FLT.Mazur
