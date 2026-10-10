/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CofinalUpperLimit
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Chart cones over an upper interval

A cartesian natural transformation pulls a test cone into a chart as soon
as its leg at one fixed stage factors through that chart. Restricting to
the stages above it constructs all the other chart legs by pullback.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u v w

variable {I : Type u} [Preorder I] {C : Type v} [Category.{w} C]
  {F G : Iᵒᵖ ⥤ C} (η : G ⟶ F) (i : I)
  (hη : ∀ j : Set.Ici i,
    IsPullback (G.map (homOfLE j.property).op) (η.app (.op j.val))
      (η.app (.op i)) (F.map (homOfLE j.property).op))
  (s : Cone F) {Y : C} (p : Y ⟶ s.pt) (q : Y ⟶ G.obj (.op i))
  (hq : q ≫ η.app (.op i) = p ≫ s.π.app (.op i))

/-- The chart leg over any stage above the fixed stage. -/
def cartesianUpperLeg (j : Set.Ici i) : Y ⟶ G.obj (.op j.val) :=
  (hη j).lift q (p ≫ s.π.app (.op j.val)) (by
    rw [Category.assoc, s.w]
    exact hq)

/-- The chart leg recovers the original test-cone component. -/
@[reassoc] theorem cartesianUpperLeg_app (j : Set.Ici i) :
    cartesianUpperLeg η i hη s p q hq j ≫ η.app (.op j.val) =
      p ≫ s.π.app (.op j.val) :=
  (hη j).lift_snd _ _ _

/-- The chart leg also recovers the given factorization at the fixed stage. -/
@[reassoc] theorem cartesianUpperLeg_map (j : Set.Ici i) :
    cartesianUpperLeg η i hη s p q hq j ≫ G.map (homOfLE j.property).op = q :=
  (hη j).lift_fst _ _ _

variable [∀ j, Mono (η.app j)]

/-- All pulled-back chart legs form a cone on the restricted inverse diagram. -/
def cartesianUpperCone : Cone ((upperStageInclusion i).op ⋙ G) where
  pt := Y
  π :=
    { app := fun j ↦ cartesianUpperLeg η i hη s p q hq j.unop
      naturality := fun j k g ↦ by
        change 𝟙 Y ≫ cartesianUpperLeg η i hη s p q hq k.unop =
          cartesianUpperLeg η i hη s p q hq j.unop ≫
            G.map (homOfLE (show k.unop.val ≤ j.unop.val from leOfHom g.unop)).op
        rw [Category.id_comp]
        apply (cancel_mono (η.app (.op k.unop.val))).1
        rw [Category.assoc, η.naturality,
          cartesianUpperLeg_app_assoc, cartesianUpperLeg_app, s.w]
        }

/-- A chart limit gives the unique lift of the pulled-back test cone. -/
def cartesianUpperLift [IsDirectedOrder I] {c : Cone G} (hc : IsLimit c) : Y ⟶ c.pt :=
  (upperStageIsLimit i hc).lift (cartesianUpperCone η i hη s p q hq)

/-- The constructed chart lift has all the required original cone components. -/
@[reassoc] theorem cartesianUpperLift_app [IsDirectedOrder I]
    {c : Cone G} (hc : IsLimit c) (j : Set.Ici i) :
    cartesianUpperLift η i hη s p q hq hc ≫ c.π.app (.op j.val) ≫ η.app (.op j.val) =
      p ≫ s.π.app (.op j.val) := by
  have hf : cartesianUpperLift η i hη s p q hq hc ≫ c.π.app (.op j.val) =
      cartesianUpperLeg η i hη s p q hq j :=
    (upperStageIsLimit i hc).fac (cartesianUpperCone η i hη s p q hq) (.op j)
  rw [← Category.assoc, hf, cartesianUpperLeg_app]

end FLT.Mazur.Approximation
