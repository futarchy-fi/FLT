/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AlgebraicClosureEmbeddingConjugacy

/-!
# Algebraic embeddings into arbitrary larger coefficient fields

Every embedding of an algebraic residue field into K factors through the
fixed algebraic closure L inside K. Relative to any chosen L-embedding,
the factor differs by an actual k-automorphism of L. K need not be algebraic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.AlgebraicEmbeddingTranscendentalFactor
variable {k E L K : Type*} [Field k] [Field E] [Field L] [Field K]
  [Algebra k E] [Algebra k L] [Algebra k K] [Algebra L K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k E] [IsAlgClosed L]

/-- Every whole algebraic embedding into the larger field comes from the fixed closure. -/
theorem exists_factor (v : E →ₐ[k] K) :
    ∃ w : E →ₐ[k] L, (IsScalarTower.toAlgHom k L K).comp w = v := by
  let e := Algebra.IsAlgebraic.algHomEquivAlgHomOfSplits (F := k) (K := E) K L
    (fun _ ↦ IsAlgClosed.splits _)
  obtain ⟨w, hw⟩ := e.surjective v
  refine ⟨w, ?_⟩
  ext x
  exact DFunLike.congr_fun hw x

/-- Independent embeddings factor through conjugates in L even when K is transcendental. -/
theorem exists_conjugate_factor [Algebra.IsAlgebraic k L]
    (u : E →ₐ[k] L) (v : E →ₐ[k] K) :
    ∃ σ : L ≃ₐ[k] L,
      (IsScalarTower.toAlgHom k L K).comp (σ.toAlgHom.comp u) = v := by
  obtain ⟨w, hw⟩ := exists_factor (L := L) v
  obtain ⟨σ, hσ⟩ := AlgebraicClosureEmbeddingConjugacy.exists_conjugacy u w
  exact ⟨σ, by rw [hσ, hw]⟩

end FLT.Mazur.AlgebraicEmbeddingTranscendentalFactor
