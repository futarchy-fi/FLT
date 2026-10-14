/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mon

/-!
# Evaluating relative monoid multiplication at its actual unit section

These are equations of scheme morphisms on arbitrary test schemes, including
nonreduced ones. Both inputs retain their specified common base morphism.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.SchemeMonoidUnitEvaluation
universe u
variable {S X : Scheme.{u}} (G : Over S) [MonObj G]
  (s : X ⟶ S) (f : X ⟶ G.left) (hf : f ≫ G.hom = s)

include hf

/-- Multiplication by the unit section on the left fixes the entire test-scheme morphism. -/
theorem left_unit (hc : (s ≫ (η[G]).left) ≫ G.hom = f ≫ G.hom) :
    pullback.lift (s ≫ (η[G]).left) f hc ≫ (μ[G]).left = f := by
  let F : Over.mk s ⟶ G := Over.homMk f hf
  let B : Over.mk s ⟶ 𝟙_ (Over S) := Over.homMk s (by simp)
  exact congrArg Over.Hom.left (MonObj.lift_comp_one_left B F)

/-- Multiplication by the unit section on the right fixes the entire test-scheme morphism. -/
theorem right_unit (hc : f ≫ G.hom = (s ≫ (η[G]).left) ≫ G.hom) :
    pullback.lift f (s ≫ (η[G]).left) hc ≫ (μ[G]).left = f := by
  let F : Over.mk s ⟶ G := Over.homMk f hf
  let B : Over.mk s ⟶ 𝟙_ (Over S) := Over.homMk s (by simp)
  exact congrArg Over.Hom.left (MonObj.lift_comp_one_right F B)

end FLT.Mazur.SchemeMonoidUnitEvaluation
