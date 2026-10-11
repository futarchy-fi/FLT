/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-!
# Sections of an actual scheme pullback

A relative point over a base map gives a section of the actual pullback.
Projection determines the section uniquely and commutes with family morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.OverPullbackSection
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T : Scheme.{u}} (f : T ⟶ S) (G : Over S)

/-- The section of the actual pullback supplied by a relative scheme point. -/
def lift (p : Over.mk f ⟶ G) : 𝟙_ (Over T) ⟶ (Over.pullback f).obj G :=
  Over.homMk (pullback.lift p.left (𝟙 T) (p.w.trans (Category.id_comp f).symm))
    (pullback.lift_snd _ _ _)

/-- Projection of the lifted section is the original relative point. -/
@[reassoc] theorem lift_fst (p : Over.mk f ⟶ G) :
    (lift f G p).left ≫ pullback.fst G.hom f = p.left :=
  pullback.lift_fst _ _ _

/-- Sections are determined by their original family projection. -/
theorem hom_ext {V : Over T} (p q : V ⟶ (Over.pullback f).obj G)
    (h : p.left ≫ pullback.fst G.hom f = q.left ≫ pullback.fst G.hom f) : p = q := by
  apply Over.OverMorphism.ext
  exact pullback.hom_ext h (p.w.trans q.w.symm)

/-- Lifting a point and then mapping its family equals lifting the mapped point. -/
theorem lift_map {H : Over S} (e : G ⟶ H) (p : Over.mk f ⟶ G) :
    lift f G p ≫ (Over.pullback f).map e = lift f H (p ≫ e) := by
  apply hom_ext
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  rw [← Category.assoc, lift_fst, lift_fst, Over.comp_left]

end FLT.Mazur.OverPullbackSection
