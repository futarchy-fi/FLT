/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedCommutativity
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The internal grading of the section algebra

The homogeneous submodules are the ranges of the actual degree inclusions.
An explicit inverse to recomposition supplies Mathlib's internal grading.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open scoped DirectSum
universe u
namespace FLT.Mazur.SectionGradedSum
open SectionGradedMultiplication
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) (U : X.Opens)

/-- Structure-sheaf scalars act centrally in the tensor-degree ring. -/
instance gradedScalarAlgebra : DirectSum.GAlgebra Γ(X, U) (Piece L U) where
  toFun := { toFun := fun r ↦ r, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
  map_one := rfl
  map_mul r s := by
    change (⟨0, r * s⟩ : GradedMonoid (Piece L U)) = ⟨0 + 0, mul L U 0 0 r s⟩
    rw [SectionGradedMultiplication.zero_mul]
    rfl
  commutes r := by
    rintro ⟨n, s⟩
    change (⟨0 + n, mul L U 0 n r s⟩ : GradedMonoid (Piece L U)) =
      ⟨n + 0, mul L U n 0 s r⟩
    rw [SectionGradedMultiplication.zero_mul, SectionGradedMultiplication.mul_zero]
    exact sigma_cast L U _ _
  smul_def r := by
    rintro ⟨n, s⟩
    change (⟨n, r • s⟩ : GradedMonoid (Piece L U)) = ⟨0 + n, mul L U 0 n r s⟩
    rw [SectionGradedMultiplication.zero_mul]
    exact (sigma_cast L U _ _).symm

/-- Degree `n` as a submodule of the full section algebra. -/
def grade (n : ℕ) : Submodule Γ(X, U) (Sections L U) := LinearMap.range (of L U n)

/-- The decomposition map inserts each section into its homogeneous submodule. -/
def decomposition : Sections L U →ₗ[Γ(X, U)] ⨁ n : ℕ, grade L U n :=
  DirectSum.toModule Γ(X, U) ℕ _ (fun n ↦
    (DirectSum.lof Γ(X, U) ℕ (fun n ↦ grade L U n) n).comp (of L U n).rangeRestrict)

/-- Decomposition has the specified value on every homogeneous section. -/
lemma decomposition_of (n : ℕ) (s : Piece L U n) :
    decomposition L U (of L U n s) =
      DirectSum.lof Γ(X, U) ℕ (fun n ↦ grade L U n) n ⟨of L U n s, ⟨s, rfl⟩⟩ := by
  simp [decomposition, of]
  rfl

/-- Recomposition is inverse to decomposition on the full direct sum. -/
lemma recompose_decomposition :
    (DirectSum.coeLinearMap (grade L U)).comp (decomposition L U) = LinearMap.id := by
  ext n s : 2
  change DirectSum.coeLinearMap (grade L U) (decomposition L U (of L U n s)) = _
  rw [decomposition_of]
  simp

/-- Decomposition is inverse to recomposition on each actual homogeneous submodule. -/
lemma decomposition_recompose :
    (decomposition L U).comp (DirectSum.coeLinearMap (grade L U)) = LinearMap.id := by
  ext n s : 2
  rcases s with ⟨s, ⟨t, rfl⟩⟩
  simp only [LinearMap.comp_apply, DirectSum.lof_eq_of, DirectSum.coeLinearMap_of,
    LinearMap.id_apply]
  exact decomposition_of L U n t

/-- The homogeneous submodules give a direct-sum decomposition. -/
instance gradeDecomposition : DirectSum.Decomposition (grade L U) :=
  DirectSum.Decomposition.ofLinearMap (grade L U) (decomposition L U)
    (recompose_decomposition L U) (decomposition_recompose L U)

/-- The unit has degree zero. -/
lemma one_mem_grade : (1 : Sections L U) ∈ grade L U 0 := ⟨(1 : Γ(X, U)), rfl⟩

/-- Multiplication adds degrees in the internal grading. -/
lemma mul_mem_grade {m n : ℕ} {a b : Sections L U}
    (ha : a ∈ grade L U m) (hb : b ∈ grade L U n) : a * b ∈ grade L U (m + n) := by
  obtain ⟨s, rfl⟩ := ha
  obtain ⟨t, rfl⟩ := hb
  exact ⟨mul L U m n s t, (mul_of L U m n s t).symm⟩

/-- The full tensor-power section algebra has its canonical internal grading. -/
instance sectionGradedAlgebra : GradedAlgebra (grade L U) where
  __ := gradeDecomposition L U
  one_mem := one_mem_grade L U
  mul_mem := fun _ _ _ _ ha hb ↦ mul_mem_grade L U ha hb

end FLT.Mazur.SectionGradedSum
