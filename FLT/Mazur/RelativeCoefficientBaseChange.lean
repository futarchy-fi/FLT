/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Retaining the new ground coordinate in old coefficient models

The old coefficient target is pulled back as a scheme. Its projection retains
both the old coefficients and the new ground coordinate, including nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.RelativeCoefficientBaseChange
set_option backward.isDefEq.respectTransparency false
variable {S S' : Scheme} (a : S' ⟶ S) {A T : Over S} {B : Over S'}
  (u : (Over.map a).obj B ⟶ A) (w : A ⟶ T)

/-- The old target, with its actual changed ground base. -/
def target : Over S' := (Over.pullback a).obj T

/-- Recover the old coefficients by the pullback projection. -/
def toOld : (Over.map a).obj (target a (T := T)) ⟶ T :=
  Over.homMk (pullback.fst T.hom a) pullback.condition

/-- The projection records the new ground coordinate alongside the old coefficients. -/
def projection : B ⟶ target a (T := T) :=
  Over.homMk (pullback.lift (u.left ≫ w.left) B.hom (by
    rw [Category.assoc, w.w]
    exact u.w)) (pullback.lift_snd _ _ _)

@[reassoc]
theorem projection_toOld :
    (Over.map a).map (projection a u w) ≫ toOld a = u ≫ w := by
  apply Over.OverMorphism.ext
  change pullback.lift _ _ _ ≫ pullback.fst T.hom a = _
  exact pullback.lift_fst _ _ _

/-- Factoring the source map does not change either retained coordinate. -/
theorem projection_comp {A' : Over S} (v : A ⟶ A') (w' : A' ⟶ T) :
    projection a (u ≫ v) w' = projection a u (v ≫ w') := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext <;>
    simp only [projection, Over.homMk_left, Over.comp_left, pullback.lift_fst,
      pullback.lift_snd, Category.assoc]

/-- Equality in the new target retains both independent scheme-valued coordinates. -/
theorem projection_test_iff {Z : Scheme} (x y : Z ⟶ B.left) :
    x ≫ (projection a u w).left = y ≫ (projection a u w).left ↔
      x ≫ u.left ≫ w.left = y ≫ u.left ≫ w.left ∧ x ≫ B.hom = y ≫ B.hom := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa only [projection, Over.homMk_left, Over.comp_left, Category.assoc, pullback.lift_fst]
        using congrArg (fun z ↦ z ≫ pullback.fst T.hom a) h
    · simpa only [projection, Over.homMk_left, Category.assoc, pullback.lift_snd]
        using congrArg (fun z ↦ z ≫ pullback.snd T.hom a) h
  · rintro ⟨h₁, h₂⟩
    apply pullback.hom_ext
    · simpa only [projection, Over.homMk_left, Over.comp_left, Category.assoc, pullback.lift_fst]
        using h₁
    · simpa only [projection, Over.homMk_left, Category.assoc, pullback.lift_snd] using h₂

/-- Over an etale ground change, etale source comparisons give etale coefficient maps. -/
instance projection_etale [Etale a] [Etale u.left] [Etale w.left] :
    Etale (projection a u w).left := by
  have he : Etale ((projection a u w).left ≫ (toOld a (T := T)).left) := by
    rw [show (projection a u w).left ≫ (toOld a (T := T)).left =
      u.left ≫ w.left from congrArg Over.Hom.left (projection_toOld a u w)]
    exact inferInstanceAs (Etale (u.left ≫ w.left))
  let _ : Etale (toOld a (T := T)).left :=
    inferInstanceAs (Etale (pullback.fst T.hom a))
  exact Etale.of_comp (projection a u w).left (toOld a (T := T)).left

end FLT.Mazur.RelativeCoefficientBaseChange
