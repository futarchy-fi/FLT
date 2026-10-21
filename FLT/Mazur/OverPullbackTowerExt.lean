/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OverPullbackTowerComparison

/-!
# Extensionality and projection maps for pullback towers

The original projection determines an over-morphism into an iterated pullback.
Projection formulas keep subsequent proofs independent of pullback definitions.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.OverPullbackCoherence
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
  {S T U : C} (g : T ⟶ S) (h : U ⟶ T) (k : U ⟶ S) (w : h ≫ g = k)

/-- Maps to an iterated pullback are determined by their original projection. -/
theorem tower_hom_ext (X : Over S) {Z : Over U}
    (a b : Z ⟶ (Over.pullback h).obj ((Over.pullback g).obj X))
    (e : a.left ≫ pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g =
      b.left ≫ pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g) : a = b := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simpa only [Category.assoc, Over.pullback_obj_hom] using e
    · change (a.left ≫ pullback.fst (pullback.snd X.hom g) h) ≫
        pullback.snd X.hom g = (b.left ≫ pullback.fst (pullback.snd X.hom g) h) ≫
          pullback.snd X.hom g
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => f ≫ h) ((Over.w a).trans (Over.w b).symm)
  · exact (Over.w a).trans (Over.w b).symm

/-- Pulling back a morphism preserves its first projection. -/
@[reassoc] theorem pullback_map_fst {X Y : Over S} (f : X ⟶ Y) :
    ((Over.pullback g).map f).left ≫ pullback.fst Y.hom g =
      pullback.fst X.hom g ≫ f.left := by
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Composing into the tower comparison preserves the original projection. -/
theorem tower_comp_fst (X : Over S) {Z : Over U}
    (a : Z ⟶ (Over.pullback k).obj X) :
    (a ≫ ((towerIso g h k w).app X).hom).left ≫
      pullback.fst (pullback.snd X.hom g) h ≫ pullback.fst X.hom g =
        a.left ≫ pullback.fst X.hom k := by
  simp only [Over.comp_left, Category.assoc, Iso.app_hom, towerIso_fst_fst]

end FLT.Mazur.OverPullbackCoherence
