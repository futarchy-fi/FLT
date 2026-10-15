/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Whole residue-field embeddings are conjugate in an algebraic closure

Two embeddings, including their coefficient maps, differ by an actual
coefficient-preserving automorphism. This is the algebraic ingredient for
controlling independent geometric lifts through the same original point.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraicClosureEmbeddingConjugacy
variable {k L K : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra k K] [IsAlgClosed K] [Algebra.IsAlgebraic k K]

/-- Two whole embeddings into the same algebraic closure are related by an automorphism. -/
theorem exists_conjugacy (u v : L →ₐ[k] K) :
    ∃ σ : K ≃ₐ[k] K, σ.toAlgHom.comp u = v := by
  let _ : Algebra L K := u.toRingHom.toAlgebra
  let _ : IsScalarTower k L K := IsScalarTower.of_algHom u
  let _ : Algebra.IsAlgebraic L K := Algebra.IsAlgebraic.tower_top (K := k) L
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic
    (K := k) (L := L) (M := K) (E := K) v
  let _ : IsAlgClosure k K := ⟨inferInstance, inferInstance⟩
  exact ⟨AlgEquiv.ofBijective φ (φ.normal_bijective k K K), hφ⟩

/-- An automorphism-invariant predicate on embeddings needs to be tested only once. -/
theorem forall_of_invariant (P : (L →ₐ[k] K) → Prop)
    (hP : ∀ (σ : K ≃ₐ[k] K) u, P u → P (σ.toAlgHom.comp u))
    (u : L →ₐ[k] K) (hu : P u) : ∀ v, P v := by
  intro v
  obtain ⟨σ, hσ⟩ := exists_conjugacy u v
  exact hσ ▸ hP σ u hu

end FLT.Mazur.AlgebraicClosureEmbeddingConjugacy
