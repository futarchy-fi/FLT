/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFamilyFiniteQuotient
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Scalar extension of the bounded polynomial module

The monomial bases identify coefficient extension of each degree truncation with
the same truncation over the new ring. No finiteness or flatness of the ring map
is required.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
universe u
variable (S T I : Type u) [CommRing S] [CommRing T] [Algebra S T] (n : ℕ)

/-- The canonical bounded basis consists of the actual monomials. -/
theorem boundedPolynomialBasis_val (m : BoundedHilbertMonomials I n) :
    (boundedPolynomialBasis S I n m).val = MvPolynomial.monomial m.val 1 := by
  classical
  change ((AddMonoidAlgebra.supportedEquivFinsupp _).symm (Finsupp.single m 1)).val = _
  simp only [AddMonoidAlgebra.supportedEquivFinsupp, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply]
  exact congrArg AddMonoidAlgebra.ofCoeff
    (Finsupp.supportedEquivFinsupp_symm_single _ m (1 : S))

/-- Coefficient extension preserves the entire bounded polynomial module. -/
def boundedPolynomialBaseChangeEquiv :
    T ⊗[S] MvPolynomial.restrictTotalDegree I S n ≃ₗ[T]
      MvPolynomial.restrictTotalDegree I T n :=
  ((boundedPolynomialBasis S I n).baseChange T).equiv
    (boundedPolynomialBasis T I n) (Equiv.refl _)

/-- The comparison preserves each bounded monomial. -/
theorem boundedPolynomialBaseChangeEquiv_basis (m : BoundedHilbertMonomials I n) :
    boundedPolynomialBaseChangeEquiv S T I n
      (1 ⊗ₜ[S] boundedPolynomialBasis S I n m) = boundedPolynomialBasis T I n m := by
  rw [← Module.Basis.baseChange_apply]
  exact Module.Basis.equiv_apply _ _ _ _

/-- Inclusion into the full polynomial module commutes with scalar extension. -/
theorem boundedPolynomialBaseChangeEquiv_subtype :
    (MvPolynomial.restrictTotalDegree I T n).subtype.comp
        (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap =
      (MvPolynomial.algebraTensorAlgEquiv S T (σ := I)).toLinearMap.comp
        ((MvPolynomial.restrictTotalDegree I S n).subtype.baseChange T) := by
  apply ((boundedPolynomialBasis S I n).baseChange T).ext
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.baseChange_apply,
    boundedPolynomialBaseChangeEquiv_basis, Submodule.subtype_apply,
    LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul, boundedPolynomialBasis_val,
    MvPolynomial.map_monomial, map_one, one_smul]

/-- On any pure tensor the comparison is ordinary coefficient extension and scaling. -/
theorem boundedPolynomialBaseChangeEquiv_tmul (t : T)
    (p : MvPolynomial.restrictTotalDegree I S n) :
    (boundedPolynomialBaseChangeEquiv S T I n (t ⊗ₜ[S] p)).val =
      t • MvPolynomial.map (algebraMap S T) p.val := by
  have h := LinearMap.congr_fun (boundedPolynomialBaseChangeEquiv_subtype S T I n)
    (t ⊗ₜ[S] p)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
    LinearMap.baseChange_tmul, AlgEquiv.toLinearMap_apply,
    MvPolynomial.algebraTensorAlgEquiv_tmul] using h

end FLT.Mazur.HilbertChart
