/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedPolynomialBaseChange

/-!
# Bounded evaluation commutes with arbitrary coefficient extension

The bounded-module and quotient-algebra comparisons intertwine evaluation.
Consequently they identify the extended evaluation kernel with the actual
bounded relation kernel of the extended full ideal.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
universe u
variable (S T I : Type u) [CommRing S] [CommRing T] [Algebra S T]
  (J : Ideal (MvPolynomial I S)) (n : ℕ)

/-- Evaluation commutes with the bounded and full quotient scalar-extension comparisons. -/
theorem boundedQuotientEvaluation_baseChange :
    (boundedQuotientEvaluation T I (J.map (MvPolynomial.map (algebraMap S T))) n).comp
        (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap =
      (polynomialQuotientBaseChangeEquiv I S T J).toLinearMap.comp
        ((boundedQuotientEvaluation S I J n).baseChange T) := by
  apply ((boundedPolynomialBasis S I n).baseChange T).ext
  intro m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Module.Basis.baseChange_apply,
    boundedPolynomialBaseChangeEquiv_basis, LinearMap.baseChange_tmul]
  change Ideal.Quotient.mk _ (boundedPolynomialBasis T I n m).val =
    polynomialQuotientBaseChangeEquiv I S T J
      (1 ⊗ₜ[S] Ideal.Quotient.mk J (boundedPolynomialBasis S I n m).val)
  simp only [polynomialQuotientBaseChangeEquiv_tmul, boundedPolynomialBasis_val,
    MvPolynomial.map_monomial, map_one, one_smul]

/-- The transported extended evaluation has precisely the new coefficient-ring relations. -/
theorem boundedRelationKernel_comap_baseChange :
    (boundedRelationKernel T I (J.map (MvPolynomial.map (algebraMap S T))) n).comap
        (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap =
      LinearMap.ker ((boundedQuotientEvaluation S I J n).baseChange T) := by
  change LinearMap.ker ((boundedQuotientEvaluation T I
    (J.map (MvPolynomial.map (algebraMap S T))) n).comp
      (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap) = _
  rw [boundedQuotientEvaluation_baseChange]
  exact LinearEquiv.ker_comp (polynomialQuotientBaseChangeEquiv I S T J).toLinearEquiv _

/-- Mapping the extended evaluation kernel gives exactly the actual new bounded relations. -/
theorem boundedRelationKernel_map_baseChange :
    (LinearMap.ker ((boundedQuotientEvaluation S I J n).baseChange T)).map
        (boundedPolynomialBaseChangeEquiv S T I n).toLinearMap =
      boundedRelationKernel T I (J.map (MvPolynomial.map (algebraMap S T))) n := by
  rw [← boundedRelationKernel_comap_baseChange S T I J n]
  exact Submodule.map_comap_eq_of_surjective
    (boundedPolynomialBaseChangeEquiv S T I n).surjective _

end FLT.Mazur.HilbertChart
