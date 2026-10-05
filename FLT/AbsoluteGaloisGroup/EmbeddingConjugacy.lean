/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.AbsoluteGaloisGroup

/-!
# Change of algebraic-closure embeddings

Two embeddings of an algebraic closure differ by a source automorphism.
The associated restriction maps are conjugate, with the conjugating element
constructed from the embeddings themselves.
-/

@[expose] public noncomputable section
namespace Field.absoluteGaloisGroup
variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Restriction using a specified embedding, with the original Krull topologies. -/
def mapWithEmbedding (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Field.absoluteGaloisGroup L →ₜ* Field.absoluteGaloisGroup K := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := e.toRingHom.toAlgebra
  exact mapOfAlgebra K L

/-- Restriction is characterized by commutation with the chosen embedding. -/
theorem mapWithEmbedding_commutes (e : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (σ : Field.absoluteGaloisGroup L) (x : AlgebraicClosure K) :
    e (mapWithEmbedding e σ x) = σ (e x) := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := e.toRingHom.toAlgebra
  exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (AlgebraicClosure K) x

/-- An actual source automorphism comparing any two embeddings of the algebraic closure. -/
def embeddingChange (e f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L) :
    Field.absoluteGaloisGroup K := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := e.toRingHom.toAlgebra
  exact f.restrictNormal' (AlgebraicClosure K)

/-- The comparison is proved from normal restriction, not assumed as data. -/
theorem embeddingChange_spec (e f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (x : AlgebraicClosure K) : e (embeddingChange e f x) = f x := by
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := e.toRingHom.toAlgebra
  exact f.restrictNormal_commutes (AlgebraicClosure K) x

/-- Changing the embedding conjugates the continuous restriction map. -/
theorem mapWithEmbedding_conjugate (e f : AlgebraicClosure K →ₐ[K] AlgebraicClosure L)
    (σ : Field.absoluteGaloisGroup L) :
    mapWithEmbedding f σ = (embeddingChange e f)⁻¹ * mapWithEmbedding e σ *
      embeddingChange e f := by
  let c := embeddingChange e f
  have he : c * mapWithEmbedding f σ = mapWithEmbedding e σ * c := by
    apply AlgEquiv.ext
    intro x
    apply e.injective
    change e (c (mapWithEmbedding f σ x)) = e (mapWithEmbedding e σ (c x))
    rw [embeddingChange_spec, mapWithEmbedding_commutes, mapWithEmbedding_commutes,
      embeddingChange_spec]
  exact (eq_inv_mul_iff_mul_eq).mpr (by simpa only [mul_assoc] using he)

end Field.absoluteGaloisGroup
