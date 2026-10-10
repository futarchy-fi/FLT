/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GradedProjBaseChangeMap
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Original homogeneous degrees under quotient scalar extension

The usual tensor-quotient equivalence identifies a scalar-extended degree
with the image of the original homogeneous group in the coefficient quotient.
This comparison does not require a flat coefficient quotient.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u

namespace FLT.Mazur.GradedQuotientTensorComparison

open GradedProjBaseChangeMap

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) (I : Ideal R)

/-- The original coefficient quotient as scalar extension of the original algebra. -/
def equiv : (R ⧸ I) ⊗[R] A ≃+* A ⧸ I.map (algebraMap R A) :=
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm.toRingEquiv

/-- The tensor-quotient equivalence retains the original algebra element. -/
theorem equiv_one_tmul (a : A) :
    equiv I (1 ⊗ₜ[R] a) = Ideal.Quotient.mk _ a := by
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor A I).symm_apply_apply
    (Ideal.Quotient.mk _ a)

/-- A scalar tensor is the original scalar multiple in the actual quotient. -/
theorem equiv_tmul_mk (r : R) (a : A) :
    equiv I ((Ideal.Quotient.mk I r) ⊗ₜ[R] a) = Ideal.Quotient.mk _ (r • a) := by
  have he : (Ideal.Quotient.mk I r) ⊗ₜ[R] a = (1 : R ⧸ I) ⊗ₜ[R] (r • a) := by
    rw [← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rfl
  rw [he, equiv_one_tmul]

/-- A degree in the actual quotient is the image of its original homogeneous group. -/
def degree (d : ℕ) : AddSubgroup (A ⧸ I.map (algebraMap R A)) :=
  (𝒜 d).toAddSubgroup.map (Ideal.Quotient.mk _).toAddMonoidHom

/-- Extending scalars carries an original degree into its actual quotient image. -/
theorem equiv_mem_degree (d : ℕ) (s : (R ⧸ I) ⊗[R] A)
    (hs : s ∈ baseGrade (B := R ⧸ I) 𝒜 d) : equiv I s ∈ degree 𝒜 I d := by
  obtain ⟨t, rfl⟩ := hs
  induction t using TensorProduct.inductionOn with
  | tmul r a =>
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    change equiv I ((Ideal.Quotient.mk I r) ⊗ₜ[R] (a : A)) ∈ degree 𝒜 I d
    rw [equiv_tmul_mk]
    exact ⟨r • (a : A), (𝒜 d).smul_mem r a.property, rfl⟩
  | add s t hs ht =>
    simpa only [map_add] using (degree 𝒜 I d).add_mem hs ht

/-- The tensor-quotient equivalence preserves and reflects the original homogeneous images. -/
theorem equiv_mem_iff (d : ℕ) (s : (R ⧸ I) ⊗[R] A) :
    equiv I s ∈ degree 𝒜 I d ↔ s ∈ baseGrade (B := R ⧸ I) 𝒜 d := by
  constructor
  · rintro ⟨a, ha, he⟩
    have ht : (1 : R ⧸ I) ⊗ₜ[R] a = s :=
      (equiv I).injective ((equiv_one_tmul I a).trans he)
    rw [← ht]
    exact Submodule.tmul_mem_baseChange_of_mem 1 ha
  · exact equiv_mem_degree 𝒜 I d s

end FLT.Mazur.GradedQuotientTensorComparison
