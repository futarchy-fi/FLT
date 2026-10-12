/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackMapNormalization

/-!
# Normalized comparison maps of full ambient quotients

Commuting with one global quotient projection is preserved on every refinement.
Epimorphy of the projection makes the normalized comparison unique.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackMapNormalization
open SheafPullbackPathComparison
universe u
variable {X Y Z : Scheme.{u}} (i : Y ⟶ X) (l : Z ⟶ Y) (j : Z ⟶ X)
  (h : l ≫ i = j)
variable {S Q P : X.Modules} (q : S ⟶ Q) (p : S ⟶ P)
attribute [local irreducible] Scheme.Modules.pullback comparison

/-- Normalization carries a full local quotient comparison to the same refined equation. -/
theorem normalize_quotient_projection
    (a : (pullback i).obj Q ⟶ (pullback i).obj P)
    (ha : (pullback i).map q ≫ a = (pullback i).map p) :
    (pullback j).map q ≫ normalize l i i j j h h a = (pullback j).map p := by
  apply (cancel_epi ((comparison l i j h).hom.app S)).mp
  rw [← (comparison l i j h).hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [normalize_comm, ← Functor.map_comp_assoc, ha]
  exact (comparison l i j h).hom.naturality p

/-- A global epimorphism determines a quotient comparison on any common refinement. -/
theorem normalize_quotient_unique [Epi q]
    {Y' : Scheme.{u}} (i' : Y' ⟶ X) (l' : Z ⟶ Y') (h' : l' ≫ i' = j)
    (a : (pullback i).obj Q ⟶ (pullback i).obj P)
    (a' : (pullback i').obj Q ⟶ (pullback i').obj P)
    (ha : (pullback i).map q ≫ a = (pullback i).map p)
    (ha' : (pullback i').map q ≫ a' = (pullback i').map p) :
    normalize l i i j j h h a = normalize l' i' i' j j h' h' a' := by
  apply (cancel_epi ((pullback j).map q)).mp
  rw [normalize_quotient_projection i l j h q p a ha,
    normalize_quotient_projection i' l' j h' q p a' ha']

end FLT.Mazur.SheafPullbackMapNormalization
