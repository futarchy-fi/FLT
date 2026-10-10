/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackPathComparison

/-!
# Refining chart recovery maps

Normalization of a recovered chart commutes with further pullback. The
proof is abstract in the schemes and modules, keeping concrete coordinate
rings out of the associativity calculation.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.ModuleSheafChartRecoveryRefinement

open SheafPullbackPathComparison

/-- A coordinate equation and a projection equation recover the original transition. -/
lemma recovery_of_projection {D : Type*} [Category* D] {G A B P Q : D}
    (a : G ⟶ A) (b : G ⟶ B) (s : A ⟶ P) (t : B ⟶ Q)
    (e : P ⟶ Q) (α : A ⟶ B) (u : G ⟶ P) (v : G ⟶ Q)
    (hu : u = a ≫ s) (hv : v = b ≫ t)
    (hc : α ≫ t = s ≫ e) (hp : a ≫ α = b) : u ≫ e = v := by
  rw [hu, hv, Category.assoc, ← hc, ← Category.assoc, hp]

variable {Z Y C X : Scheme.{u}}

/-- Refined recovery retains the original morphism after normalization of both paths. -/
lemma recovery_refine (c : Z ⟶ Y) (a : Y ⟶ C) (i : C ⟶ X)
    (r : Y ⟶ X) (b : Z ⟶ C) (t : Z ⟶ X)
    (ha : a ≫ i = r) (hb : c ≫ a = b) (hc : c ≫ r = t) (ht : b ≫ i = t)
    (G : X.Modules) (N : C.Modules) (e : (pullback i).obj G ⟶ N) :
    (comparison c r t hc).inv.app G ≫
      (pullback c).map ((comparison a i r ha).inv.app G ≫ (pullback a).map e) ≫
        (comparison c a b hb).hom.app N =
      (comparison b i t ht).inv.app G ≫ (pullback b).map e := by
  have hnorm : (comparison c r t hc).inv.app G ≫
      (pullback c).map ((comparison a i r ha).inv.app G) ≫
        (comparison c a b hb).hom.app ((pullback i).obj G) =
      (comparison b i t ht).inv.app G := by
    apply (cancel_epi ((pullback c).map ((comparison a i r ha).hom.app G) ≫
      (comparison c r t hc).hom.app G)).mp
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [← Category.assoc, comparison_assoc c a i b r t hb ha hc ht G]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    dsimp only [Functor.comp_obj]
    rw [(pullback c).map_id ((pullback a).obj ((pullback i).obj G)),
      Category.id_comp, Category.comp_id]
  rw [Functor.map_comp, Category.assoc]
  have hn := (comparison c a b hb).hom.naturality e
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc] using congrArg (fun k ↦ k ≫ (pullback b).map e) hnorm

end FLT.Mazur.ModuleSheafChartRecoveryRefinement
