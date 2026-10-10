/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatQuotientIdealBaseChange
public import FLT.Mazur.FinitePresentationSurjectiveScalars
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Finite presentation of polynomial ideals after coefficient change

The abstract flat-quotient base-change result is expressed using the actual
coefficient map on polynomial rings. This is the form used by Hilbert charts.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.FCurve
variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- A polynomial ideal with flat quotient retains finite presentation over any test ring. -/
theorem polynomialIdeal_finitePresentation_map (I : Ideal (MvPolynomial ι R))
    [Module.Flat R (MvPolynomial ι R ⧸ I)]
    [Module.FinitePresentation (MvPolynomial ι R) I] :
    Module.FinitePresentation (MvPolynomial ι S)
      (I.map (MvPolynomial.map (algebraMap R S))) := by
  let e : (MvPolynomial ι R ⊗[R] S) ≃+* MvPolynomial ι S :=
    (Algebra.TensorProduct.comm R (MvPolynomial ι R) S).toRingEquiv.trans
      (MvPolynomial.algebraTensorAlgEquiv R S).toRingEquiv
  let _ := ideal_finitePresentation_coefficientChange (R := R) S I
  have he : e.toRingHom.comp
      (algebraMap (MvPolynomial ι R) (MvPolynomial ι R ⊗[R] S)) =
        MvPolynomial.map (algebraMap R S) := by
    apply RingHom.ext
    intro p
    change MvPolynomial.algebraTensorAlgEquiv R S ((1 : S) ⊗ₜ[R] p) = _
    rw [MvPolynomial.algebraTensorAlgEquiv_tmul, one_smul]
  have h := ideal_finitePresentation_map_equiv e
    (I.map (algebraMap (MvPolynomial ι R) (MvPolynomial ι R ⊗[R] S)))
  rwa [Ideal.map_map, he] at h

end FLT.Mazur.FCurve
