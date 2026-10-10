/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Algebraically closed points lift across integral inclusions

Given an injective integral algebra, every map from the base to an
algebraically closed field extends to the algebra. Lying over supplies a prime
above the kernel; the induced integral extension of domains embeds into the
specified algebraically closed field.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteGroupQuotient

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [Algebra.IsIntegral R A] [FaithfulSMul R A]
  {K : Type*} [Field K] [IsAlgClosed K]

/-- An algebraically closed field-valued map lifts across an injective integral algebra. -/
theorem exists_ringHom_of_integral (f : R →+* K) :
    ∃ g : A →+* K, g.comp (algebraMap R A) = f := by
  let _ : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  let Q : (RingHom.ker f).primesOver A := Classical.choice inferInstance
  let _ : Algebra (R ⧸ RingHom.ker f) K := f.kerLift.toAlgebra
  let _ : FaithfulSMul (R ⧸ RingHom.ker f) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr f.kerLift_injective
  let e : (A ⧸ Q.val) →ₐ[R ⧸ RingHom.ker f] K := IsAlgClosed.lift
  refine ⟨e.toRingHom.comp (Ideal.Quotient.mk Q.val), ?_⟩
  ext r
  change e (Ideal.Quotient.mk Q.val (algebraMap R A r)) = f r
  rw [← Ideal.Quotient.algebraMap_mk_of_liesOver Q.val (RingHom.ker f) r, e.commutes]
  rfl

end FLT.Mazur.FiniteGroupQuotient
