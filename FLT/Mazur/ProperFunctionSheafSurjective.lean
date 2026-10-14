/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Surjectivity from properness and faithful functions

A proper morphism with injective pullback on affine-open functions is
schematically dominant. Its closed image is therefore the whole target.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ProperFunctionSheafSurjective

variable {X Y : Scheme} (f : X ⟶ Y) [IsProper f]

/-- Injective affine-open function maps give the zero scheme-theoretic kernel. -/
theorem ker_eq_bot (hf : ∀ U : Y.affineOpens, Function.Injective (f.app U)) :
    f.ker = ⊥ := by
  apply Scheme.IdealSheafData.ext
  funext U
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (hf U)

/-- Properness upgrades faithful functions to surjectivity on the actual target. -/
theorem surjective (hf : ∀ U : Y.affineOpens, Function.Injective (f.app U)) :
    Surjective f := by
  have hr := f.support_ker
  rw [ker_eq_bot f hf, Scheme.IdealSheafData.support_bot] at hr
  have hc : IsClosed (Set.range f) := f.isClosedMap.isClosed_range
  rw [hc.closure_eq] at hr
  constructor
  intro y
  have hy : y ∈ (⊤ : TopologicalSpace.Closeds Y) := trivial
  change y ∈ (↑(⊤ : TopologicalSpace.Closeds Y) : Set Y) at hy
  rw [hr] at hy
  exact hy

end FLT.Mazur.ProperFunctionSheafSurjective
