/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.EmbeddingConjugacy
public import FLT.Deformations.ArithmeticGaloisQuotient
public import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Embedding independence of the actual arithmetic local maps

Every choice of algebraic-closure embedding gives a continuous map into the
same arithmetic quotient. The original local map is recovered, and any
other choice is conjugate by an element of that quotient.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Deformation
open Field.absoluteGaloisGroup
variable (p q : ℕ) (hq : q.Prime)
local notation "K" => hq.toHeightOneSpectrumRingOfIntegersRat.adicCompletion ℚ

/-- The closure embedding used by the original local restriction. -/
def arithmeticLocalClosureEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K :=
  (AlgebraicClosure.map (algebraMap ℚ K)).toRatAlgHom

/-- The same arithmetic local map with an explicitly supplied closure embedding. -/
def hardlyArithmeticLocalMapWithEmbedding
    (e : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) :
    Field.absoluteGaloisGroup K →ₜ* HardlyArithmeticGaloisGroup p :=
  (hardlyArithmeticGaloisProjection p).comp (mapWithEmbedding e)

/-- The explicit canonical choice recovers the original local map pointwise. -/
theorem hardlyArithmeticLocalMapWithEmbedding_original (g : Field.absoluteGaloisGroup K) :
    hardlyArithmeticLocalMapWithEmbedding p q hq (arithmeticLocalClosureEmbedding q hq) g =
      hardlyArithmeticLocalMap p q hq g := by
  apply congrArg (hardlyArithmeticGaloisProjection p)
  apply AlgEquiv.ext
  intro x
  apply (AlgebraicClosure.map (algebraMap ℚ K)).injective
  exact (mapWithEmbedding_commutes (arithmeticLocalClosureEmbedding q hq) g x).trans
    (Field.absoluteGaloisGroup.lift_map (algebraMap ℚ K) g x).symm

/-- Changing the closure embedding conjugates the actual local map inside G_S. -/
theorem hardlyArithmeticLocalMapWithEmbedding_conjugate
    (e : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K) :
    ∃ c : HardlyArithmeticGaloisGroup p, ∀ g : Field.absoluteGaloisGroup K,
      hardlyArithmeticLocalMapWithEmbedding p q hq e g =
        c⁻¹ * hardlyArithmeticLocalMap p q hq g * c := by
  let e₀ := arithmeticLocalClosureEmbedding q hq
  refine ⟨hardlyArithmeticGaloisProjection p (embeddingChange e₀ e), fun g ↦ ?_⟩
  have h := congrArg (hardlyArithmeticGaloisProjection p) (mapWithEmbedding_conjugate e₀ e g)
  rw [map_mul, map_mul, map_inv] at h
  change hardlyArithmeticLocalMapWithEmbedding p q hq e g =
    _ * hardlyArithmeticLocalMapWithEmbedding p q hq e₀ g * _ at h
  rwa [hardlyArithmeticLocalMapWithEmbedding_original] at h

end Deformation
