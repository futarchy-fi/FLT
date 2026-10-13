/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Scalar extension of an actual polynomial quotient

The tensor product of the original quotient is the polynomial algebra over
the new coefficients modulo the actual extended ideal. The comparison keeps
the coefficient scalars and all original polynomial classes.
-/

@[expose] public noncomputable section
open MvPolynomial TensorProduct
namespace FLT.Mazur.PolynomialQuotientScalarExtension
set_option backward.isDefEq.respectTransparency false
variable {σ R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
  (I : Ideal (MvPolynomial σ R))

/-- The polynomial tensor comparison sends the full extended ideal to the coefficient image. -/
theorem map_ideal :
    (I.map (Algebra.TensorProduct.includeRight (A := S) (R := R))).map
      (algebraTensorAlgEquiv R S).toRingHom = I.map (map (algebraMap R S)) := by
  change (I.map (Algebra.TensorProduct.includeRight
    (A := S) (B := MvPolynomial σ R) (R := R)).toRingHom).map _ = _
  rw [Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  change algebraTensorAlgEquiv R S (1 ⊗ₜ[R] p) = map (algebraMap R S) p
  rw [algebraTensorAlgEquiv_tmul, one_smul]

/-- A coefficient-preserving equivalence with the quotient by the unchanged extended ideal. -/
def equiv : S ⊗[R] (MvPolynomial σ R ⧸ I) ≃ₐ[S]
    MvPolynomial σ S ⧸ I.map (map (algebraMap R S)) :=
  (Algebra.TensorProduct.tensorQuotientEquiv S (MvPolynomial σ R) S I).trans
    (Ideal.quotientEquivAlg _ _ (algebraTensorAlgEquiv R S) (map_ideal S I).symm)

/-- Original polynomial classes and new scalars are retained on every pure tensor. -/
theorem equiv_tmul (a : S) (p : MvPolynomial σ R) :
    equiv S I (a ⊗ₜ[R] Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk _ (a • map (algebraMap R S) p) := by
  simp only [equiv, AlgEquiv.trans_apply, Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul,
    Ideal.quotientEquivAlg_mk, algebraTensorAlgEquiv_tmul]

end FLT.Mazur.PolynomialQuotientScalarExtension
