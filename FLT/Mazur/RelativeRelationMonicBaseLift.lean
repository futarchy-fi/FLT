/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic

/-!
# Lifting both relation endpoints through a monic coefficient base

When the source is unchanged up to isomorphism, monicity of the coefficient
base gives the original relation a unique compatible local base structure.
Both independent endpoints lift, and forgetting the local base recovers the
entire original relation object.
-/

@[expose] public noncomputable section
open CategoryTheory
universe v u
namespace FLT.Mazur.MonicBaseRelation
variable {C : Type u} [Category.{v} C] {S S' : C} (a : S' ⟶ S) [Mono a]
  {D A : Over S} {B : Over S'} (p q : D ⟶ A) (u : (Over.map a).obj B ≅ A)

/-- The original relation with the base structure induced by its first endpoint. -/
def localObject : Over S' := Over.mk ((p ≫ u.inv).left ≫ B.hom)

/-- The first endpoint lifts with its original underlying map. -/
def localFst : localObject a p u ⟶ B := Over.homMk (p ≫ u.inv).left rfl

/-- Monicity forces the second endpoint to have the same local base structure. -/
def localSnd : localObject a p u ⟶ B := Over.homMk (q ≫ u.inv).left (by
  apply (cancel_mono a).mp
  change ((q ≫ u.inv).left ≫ B.hom) ≫ a =
    ((p ≫ u.inv).left ≫ B.hom) ≫ a
  rw [Category.assoc, Category.assoc]
  exact (Over.w (q ≫ u.inv)).trans (Over.w (p ≫ u.inv)).symm)

/-- Forgetting the local base retains literally the original relation object. -/
def originalIso : (Over.map a).obj (localObject a p u) ≅ D :=
  Over.isoMk (Iso.refl _) (by
    change (𝟙 _) ≫ D.hom = ((p ≫ u.inv).left ≫ B.hom) ≫ a
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (p ≫ u.inv)).symm)

omit [Mono a] in
/-- The first endpoint is unchanged after forgetting the local base. -/
@[reassoc]
theorem localFst_original :
    (Over.map a).map (localFst a p u) ≫ u.hom = (originalIso a p u).hom ≫ p := by
  apply Over.OverMorphism.ext
  change (p.left ≫ u.inv.left) ≫ u.hom.left = (𝟙 _) ≫ p.left
  have h : (p ≫ u.inv) ≫ u.hom = p := by simp only [Category.assoc,
    u.inv_hom_id, Category.comp_id]
  simpa only [Over.comp_left, Category.id_comp] using congrArg Over.Hom.left h

/-- The second endpoint remains independent and is also unchanged. -/
@[reassoc]
theorem localSnd_original :
    (Over.map a).map (localSnd a p q u) ≫ u.hom = (originalIso a p u).hom ≫ q := by
  apply Over.OverMorphism.ext
  change (q.left ≫ u.inv.left) ≫ u.hom.left = (𝟙 _) ≫ q.left
  have h : (q ≫ u.inv) ≫ u.hom = q := by simp only [Category.assoc,
    u.inv_hom_id, Category.comp_id]
  simpa only [Over.comp_left, Category.id_comp] using congrArg Over.Hom.left h

end FLT.Mazur.MonicBaseRelation
