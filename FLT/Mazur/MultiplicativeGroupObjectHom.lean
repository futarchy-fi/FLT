/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# Multiplicative maps into group objects preserve the identity

Cancellation in the group of points proves identity preservation from the
multiplication equation. No separate normalization of the lift is needed.
-/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.MultiplicativeGroupObjectHom

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {M N : C} [MonObj M] [GrpObj N] (f : M ⟶ N)
  (hf : μ[M] ≫ f = (f ⊗ₘ f) ≫ μ[N])

include hf in
/-- The multiplication equation on objects gives multiplication on every point group. -/
theorem points_mul {X : C} (a b : X ⟶ M) :
    (a * b) ≫ f = (a ≫ f) * (b ≫ f) := by
  simp only [Hom.mul_def, Category.assoc, hf, ← lift_map_assoc]

include hf in
/-- An object map preserving multiplication into a group object preserves its identity. -/
theorem isMonHom : IsMonHom f where
  mul_hom := hf
  one_hom := by
    have he := points_mul f hf (1 : 𝟙_ C ⟶ M) 1
    rw [_root_.one_mul] at he
    have ho : (1 : 𝟙_ C ⟶ M) ≫ f = 1 := _root_.mul_eq_left.mp he.symm
    simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using ho

end FLT.Mazur.MultiplicativeGroupObjectHom
