/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeOverlapRefinement

/-!
# The categorical triple overlap of a scheme morphism

The triple overlap is the fiber product of two double overlaps over their
common middle coordinate. Its three pair maps support the geometric cocycle.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeTripleOverlap
variable {X Y : Scheme.{u}} (p : Y ⟶ X)

/-- Three points over the same base, presented using their adjacent pairs. -/
abbrev triple : Scheme.{u} :=
  Limits.pullback (Limits.pullback.snd p p) (Limits.pullback.fst p p)

/-- The first two coordinates. -/
abbrev pair12 : triple p ⟶ Limits.pullback p p := Limits.pullback.fst _ _

/-- The last two coordinates. -/
abbrev pair23 : triple p ⟶ Limits.pullback p p := Limits.pullback.snd _ _

/-- The first coordinate. -/
abbrev coord1 : triple p ⟶ Y := pair12 p ≫ Limits.pullback.fst p p

/-- The middle coordinate. -/
abbrev coord2 : triple p ⟶ Y := pair12 p ≫ Limits.pullback.snd p p

/-- The last coordinate. -/
abbrev coord3 : triple p ⟶ Y := pair23 p ≫ Limits.pullback.snd p p

/-- The two presentations of the middle coordinate agree. -/
@[reassoc]
theorem pair23_fst : pair23 p ≫ Limits.pullback.fst p p = coord2 p :=
  Limits.pullback.condition.symm

/-- The first and last coordinates have the same image in the base. -/
theorem coord13_base : coord1 p ≫ p = coord3 p ≫ p := by
  have hm : pair12 p ≫ Limits.pullback.snd p p =
      pair23 p ≫ Limits.pullback.fst p p := Limits.pullback.condition
  simp only [coord1, coord3, Category.assoc]
  rw [Limits.pullback.condition, ← Category.assoc, hm, Category.assoc,
    Limits.pullback.condition]

/-- The first and last coordinates form the third pair. -/
def pair13 : triple p ⟶ Limits.pullback p p :=
  Limits.pullback.lift (coord1 p) (coord3 p) (coord13_base p)

@[reassoc (attr := simp)]
theorem pair13_fst : pair13 p ≫ Limits.pullback.fst p p = coord1 p :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem pair13_snd : pair13 p ≫ Limits.pullback.snd p p = coord3 p :=
  Limits.pullback.lift_snd _ _ _

variable {X' Y' : Scheme.{u}} (q : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
variable (w : q ≫ a = b ≫ p)

/-- A refinement square induces the map of actual triple overlaps. -/
def refinement : triple q ⟶ triple p :=
  Limits.pullback.lift
    (pair12 q ≫ SchemeOverlapRefinement.overlapMap p q a b w)
    (pair23 q ≫ SchemeOverlapRefinement.overlapMap p q a b w) (by
      simp only [Category.assoc, SchemeOverlapRefinement.overlapMap_fst,
        SchemeOverlapRefinement.overlapMap_snd]
      rw [← Category.assoc, ← Category.assoc, pair23_fst])

@[reassoc (attr := simp)]
theorem refinement_pair12 : refinement p q a b w ≫ pair12 p =
    pair12 q ≫ SchemeOverlapRefinement.overlapMap p q a b w :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem refinement_pair23 : refinement p q a b w ≫ pair23 p =
    pair23 q ≫ SchemeOverlapRefinement.overlapMap p q a b w :=
  Limits.pullback.lift_snd _ _ _

@[reassoc]
theorem refinement_coord1 : refinement p q a b w ≫ coord1 p = coord1 q ≫ b := by
  simp only [coord1, refinement_pair12_assoc,
    Category.assoc, SchemeOverlapRefinement.overlapMap_fst]

@[reassoc]
theorem refinement_coord2 : refinement p q a b w ≫ coord2 p = coord2 q ≫ b := by
  simp only [coord2, refinement_pair12_assoc,
    Category.assoc, SchemeOverlapRefinement.overlapMap_snd]

@[reassoc]
theorem refinement_coord3 : refinement p q a b w ≫ coord3 p = coord3 q ≫ b := by
  simp only [coord3, refinement_pair23_assoc,
    Category.assoc, SchemeOverlapRefinement.overlapMap_snd]

@[reassoc (attr := simp)]
theorem refinement_pair13 : refinement p q a b w ≫ pair13 p =
    pair13 q ≫ SchemeOverlapRefinement.overlapMap p q a b w := by
  apply Limits.pullback.hom_ext
  · simp only [Category.assoc, pair13_fst, SchemeOverlapRefinement.overlapMap_fst,
      refinement_coord1, pair13_fst_assoc]
  · simp only [Category.assoc, pair13_snd, SchemeOverlapRefinement.overlapMap_snd,
      refinement_coord3, pair13_snd_assoc]

end FLT.Mazur.SchemeTripleOverlap
