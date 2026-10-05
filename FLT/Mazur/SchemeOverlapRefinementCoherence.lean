/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinement

/-!
# Coherence of the maps between refined overlaps

The canonical maps of double overlaps preserve the diagonal, identities, and
composition. These are equations of the actual scheme morphisms, proved from
the fiber-product universal property.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeOverlapRefinement
variable {X Y X' Y' X'' Y'' : Scheme.{u}}
variable (p : Y ⟶ X) (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- The overlap refinement sends the refined diagonal to the original diagonal. -/
@[reassoc]
theorem diagonal_overlapMap :
    Limits.pullback.diagonal q ≫ overlapMap p q a b w = b ≫ Limits.pullback.diagonal p := by
  apply Limits.pullback.hom_ext <;> simp

/-- The identity refinement induces the identity map on the double overlap. -/
@[simp]
theorem overlapMap_id : overlapMap p p (𝟙 X) (𝟙 Y) (by simp) = 𝟙 _ := by
  apply Limits.pullback.hom_ext <;> simp

variable (r : Y'' ⟶ X'') (a' : X'' ⟶ X') (b' : Y'' ⟶ Y')
variable (w' : r ≫ a' = b' ≫ q)

include w w' in
/-- Composable refinement squares give the composite refinement square. -/
theorem square_comp : r ≫ (a' ≫ a) = (b' ≫ b) ≫ p := by
  rw [← Category.assoc, w', Category.assoc, w, ← Category.assoc]

/-- Maps of categorical double overlaps compose exactly. -/
@[reassoc]
theorem overlapMap_comp :
    overlapMap q r a' b' w' ≫ overlapMap p q a b w =
      overlapMap p r (a' ≫ a) (b' ≫ b) (square_comp p q a b w r a' b' w') := by
  apply Limits.pullback.hom_ext <;> simp [Category.assoc]

end FLT.Mazur.SchemeOverlapRefinement
