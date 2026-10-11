/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PullbackRotationTransport

/-!
# Transport of overlap rotations by a pullback-preserving functor

Projection equations and cyclic identities survive the canonical pullback
comparisons. These abstract lemmas keep geometric reductions out of the proofs.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace FLT.Mazur

variable {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
  {A B E P Q T Z : C} (l : A ⟶ E) (m : B ⟶ E) (n : P ⟶ T) (p : Q ⟶ T)
  [HasPullback l m] [HasPullback n p]
  [HasPullback (F.map l) (F.map m)] [HasPullback (F.map n) (F.map p)]
  [PreservesLimit (cospan l m) F] [PreservesLimit (cospan n p) F]

/-- Transport a coordinate on the original full pullback. -/
def mappedPullbackCoordinate (c : pullback l m ⟶ Z) :
    pullback (F.map l) (F.map m) ⟶ F.obj Z :=
  (PreservesPullback.iso F l m).inv ≫ F.map c

/-- A rotation equation for a coordinate survives canonical pullback transport. -/
theorem mappedPullbackRotation_coordinate (r : pullback l m ⟶ pullback n p)
    (c : pullback n p ⟶ Z) (d : pullback l m ⟶ Z) (h : r ≫ c = d) :
    mappedPullbackRotation F l m n p r ≫ mappedPullbackCoordinate F n p c =
      mappedPullbackCoordinate F l m d := by
  simp only [mappedPullbackRotation, mappedPullbackCoordinate, Category.assoc,
    Iso.hom_inv_id_assoc, ← F.map_comp, h]

end FLT.Mazur
