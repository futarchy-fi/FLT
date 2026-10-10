/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The determinant criterion for a prescribed polynomial basis

A tuple in a finite free module is a basis exactly when its coordinate
determinant is a unit. Its determinant commutes with arbitrary base change.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable {S A : Type*} [CommRing S] [CommRing A] [Algebra S A] {d : ℕ}
variable (b : Module.Basis (Fin d) S A) (y : Fin d → A)

/-- The determinant of the actual coordinate matrix of a proposed basis. -/
def basisDeterminant : S := b.det y

/-- The actual determinant criterion constructs a basis with precisely the prescribed vectors. -/
theorem exists_basis_iff_isUnit_basisDeterminant :
    (∃ c : Module.Basis (Fin d) S A, ∀ i, c i = y i) ↔ IsUnit (basisDeterminant b y) := by
  constructor
  · rintro ⟨c, hc⟩
    have h : y = c := funext fun i ↦ (hc i).symm
    rw [basisDeterminant, h]
    exact b.isUnit_det c
  · intro h
    obtain ⟨hli, hspan⟩ := (b.is_basis_iff_det).mpr h
    exact ⟨Module.Basis.mk hli hspan.ge, fun i ↦ Module.Basis.mk_apply _ _ i⟩

variable (T : Type*) [CommRing T] [Algebra S T]

/-- The actual proposed basis tuple in the scalar extension. -/
def baseChangedTuple (i : Fin d) : T ⊗[S] A := 1 ⊗ₜ y i

/-- The coordinate matrix after base change is the entrywise scalar image. -/
theorem basisMatrix_baseChange :
    (b.baseChange T).toMatrix (baseChangedTuple y T) =
      (b.toMatrix y).map (algebraMap S T) := by
  ext i j
  change (b.baseChange T).repr ((1 : T) ⊗ₜ[S] y j) i = algebraMap S T (b.repr (y j) i)
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]

/-- The actual basis determinant commutes with arbitrary base change. -/
theorem basisDeterminant_baseChange :
    basisDeterminant (A := T ⊗[S] A) (b.baseChange T) (baseChangedTuple y T) =
      algebraMap S T (basisDeterminant b y) := by
  rw [basisDeterminant, Module.Basis.det_apply, basisMatrix_baseChange]
  exact ((algebraMap S T).map_det (b.toMatrix y)).symm

/-- Scalar extension admits the prescribed basis exactly when its determinant is a unit. -/
theorem baseChange_exists_basis_iff :
    (∃ c : Module.Basis (Fin d) T (T ⊗[S] A), ∀ i, c i = baseChangedTuple y T i) ↔
      IsUnit (algebraMap S T (basisDeterminant b y)) := by
  rw [exists_basis_iff_isUnit_basisDeterminant (b.baseChange T), basisDeterminant_baseChange]

end FLT.Mazur.HilbertChart
