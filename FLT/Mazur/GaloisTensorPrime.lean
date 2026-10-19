/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Every prime of the algebraic-closure overlap is a Galois evaluation

For an algebraic algebraically closed extension L/K, every prime of
L tensor_K L is the kernel of r tensor s maps to r times g(s).
This supplies all points of the coefficient overlap needed in scheme descent.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.GaloisTensorPrime

universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- Evaluate the original tensor overlap at a relative field automorphism. -/
def evaluation (g : L ≃ₐ[K] L) : L ⊗[K] L →ₐ[L] L :=
  AlgHom.liftEquiv K L L L g.toAlgHom

/-- Evaluation retains the two original coefficient embeddings. -/
theorem evaluation_tmul (g : L ≃ₐ[K] L) (r s : L) :
    evaluation g (r ⊗ₜ[K] s) = r * g s := rfl

variable [Algebra.IsAlgebraic K L]

/-- Every field-valued map of the coefficient overlap comes from an automorphism. -/
theorem exists_evaluation (f : L ⊗[K] L →ₐ[L] L) :
    ∃ g : L ≃ₐ[K] L, evaluation g = f := by
  let a := (AlgHom.liftEquiv K L L L).symm f
  refine ⟨AlgEquiv.ofBijective a (Algebra.IsAlgebraic.algHom_bijective a), ?_⟩
  exact (AlgHom.liftEquiv K L L L).apply_symm_apply f

variable [IsAlgClosed L]

/-- Every original prime ideal of the overlap is the kernel of a Galois evaluation. -/
theorem exists_evaluation_ker (P : Ideal (L ⊗[K] L)) [P.IsPrime] :
    ∃ g : L ≃ₐ[K] L, RingHom.ker (evaluation g).toRingHom = P := by
  let e : L ≃ₐ[L] ((L ⊗[K] L) ⧸ P) :=
    AlgEquiv.ofBijective (Algebra.ofId L _) IsAlgClosed.algebraMap_bijective_of_isIntegral
  let f := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ L P)
  obtain ⟨g, hg⟩ := exists_evaluation f
  refine ⟨g, ?_⟩
  rw [hg]
  ext x
  change e.symm (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [← map_zero e.symm, e.symm.injective.eq_iff, Ideal.Quotient.eq_zero_iff_mem]

/-- The actual prime point of the original overlap supplied by a Galois automorphism. -/
def prime (g : L ≃ₐ[K] L) : PrimeSpectrum (L ⊗[K] L) :=
  ⟨RingHom.ker (evaluation g).toRingHom, RingHom.ker_isPrime _⟩

/-- Galois evaluations cover every point, not just closed points, of the coefficient overlap. -/
theorem prime_surjective : Function.Surjective (prime (K := K) (L := L)) := by
  intro P
  obtain ⟨g, hg⟩ := exists_evaluation_ker P.asIdeal
  exact ⟨g, PrimeSpectrum.ext hg⟩

end FLT.Mazur.GaloisTensorPrime
