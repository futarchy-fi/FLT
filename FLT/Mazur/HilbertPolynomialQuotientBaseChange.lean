/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartQuotientBasis
public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Actual base change of ambient polynomial quotient ideals

Scalar extension of an arbitrary polynomial quotient is the quotient by the
extended ideal. The comparison includes an explicit formula on pure tensors.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace FLT.Mazur.HilbertChart

variable (I : Type*) (S T : Type*) [CommRing S] [CommRing T] [Algebra S T]

/-- Polynomial scalar extension identifies tensor inclusion with coefficient extension. -/
theorem polynomialTensor_inclusion :
    (MvPolynomial.algebraTensorAlgEquiv S T (σ := I)).toRingHom.comp
      (Algebra.TensorProduct.includeRight : MvPolynomial I S →ₐ[S]
        T ⊗[S] MvPolynomial I S).toRingHom = MvPolynomial.map (algebraMap S T) := by
  apply RingHom.ext
  intro p
  change MvPolynomial.algebraTensorAlgEquiv S T ((1 : T) ⊗ₜ[S] p) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]

/-- The tensor polynomial comparison carries the extended ideal to coefficient extension. -/
theorem polynomialTensor_ideal (J : Ideal (MvPolynomial I S)) :
    J.map (MvPolynomial.map (algebraMap S T)) =
      (J.map (Algebra.TensorProduct.includeRight : MvPolynomial I S →ₐ[S]
        T ⊗[S] MvPolynomial I S).toRingHom).map
          (MvPolynomial.algebraTensorAlgEquiv S T (σ := I)).toRingHom := by
  rw [Ideal.map_map, polynomialTensor_inclusion]

/-- The actual tensor base change of a polynomial quotient is the extended-ideal quotient. -/
def polynomialQuotientBaseChangeEquiv (J : Ideal (MvPolynomial I S)) :
    T ⊗[S] (MvPolynomial I S ⧸ J) ≃ₐ[T]
      MvPolynomial I T ⧸ J.map (MvPolynomial.map (algebraMap S T)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv T (MvPolynomial I S) T J).trans
    (Ideal.quotientEquivAlg _ _ (MvPolynomial.algebraTensorAlgEquiv S T)
      (polynomialTensor_ideal I S T J))

/-- On pure tensors the quotient comparison extends polynomial coefficients. -/
theorem polynomialQuotientBaseChangeEquiv_tmul (J : Ideal (MvPolynomial I S))
    (t : T) (p : MvPolynomial I S) :
    polynomialQuotientBaseChangeEquiv I S T J (t ⊗ₜ Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk (J.map (MvPolynomial.map (algebraMap S T)))
        (t • MvPolynomial.map (algebraMap S T) p) := by
  change Ideal.Quotient.mk _
    (MvPolynomial.algebraTensorAlgEquiv S T (t ⊗ₜ[S] p)) = _
  rw [MvPolynomial.algebraTensorAlgEquiv_tmul]

/-- The actual base-change isomorphism preserves every ambient generator. -/
theorem polynomialQuotientBaseChangeEquiv_generator (J : Ideal (MvPolynomial I S)) (i : I) :
    polynomialQuotientBaseChangeEquiv I S T J ((1 : T) ⊗ₜ[S] quotientGenerator I S J i) =
      quotientGenerator I T (J.map (MvPolynomial.map (algebraMap S T))) i := by
  rw [quotientGenerator, polynomialQuotientBaseChangeEquiv_tmul,
    MvPolynomial.map_X, one_smul, quotientGenerator]

end FLT.Mazur.HilbertChart
