/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentBranches
public import FLT.Mazur.WeierstrassModificationXInvolution
public import FLT.Mazur.WeierstrassModificationXNodeInverseFunctions
public import FLT.Mazur.NilpotentPolynomialEvaluation

/-!
# Original Laurent branches lie in the full node neighborhoods

The small Laurent branch makes the first node denominator a unit.
Reflection exchanges the two independently constructed original Laurent maps.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => R[T;T⁻¹]
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6

/-- The original small Laurent map sends the full first node denominator to a unit. -/
theorem laurentBranchEvaluation_node_unit (r : Polynomial R) (hrI : r ∈ I.map Polynomial.C) :
    IsUnit (E false (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)) := by
  rw [map_add, AlgHom.commutes, polynomialSmallFactor, map_sub, hom_polynomial_incidence]
  simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentSlopeEvaluation_t]
  change IsUnit (nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 -
    r.eval₂ (algebraMap R B) (LaurentPolynomial.T (-1)) + algebraMap R B W.a₁)
  have hn := NilpotentQuadraticRoot.element_nilpotent _ (laurentArithmeticIdeal_nilpotent I hI)
    ((laurentArithmeticIdeal I).sub_mem
      (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
      (NilpotentPolynomialInverse.eval₂_mem I (algebraMap R B) r hrI (LaurentPolynomial.T (-1))))
  exact hn.isUnit_add_right_of_commute (ha.map (algebraMap R B)) (mul_comm _ _)

/-- The original full reflection exchanges the two Laurent labels on every function. -/
theorem laurentBranchEvaluation_reflection :
    (E false).comp ((initialReflection W s b3 b4 b6).restrictScalars R).toAlgHom =
      E true := by
  apply hom_ext
  · change E false (initialReflection W s b3 b4 b6 (t W s b3 b4 b6)) = _
    rw [initialReflection_t]
    exact (laurentSlopeEvaluation_t ..).trans (laurentSlopeEvaluation_t ..).symm
  · change E false (initialReflection W s b3 b4 b6 (v W s b3 b4 b6)) = _
    rw [initialReflection_v, map_sub, map_neg, hom_polynomial_incidence]
    simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentSlopeEvaluation_t]
    change -nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 -
      (polynomialSlopeLinear W b3).eval₂ (algebraMap R B) (LaurentPolynomial.T (-1)) =
        QuadraticRootBranchLocalization.oppositeRoot (laurentSlopeLinear W b3)
          (nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    simp only [polynomialSlopeLinear, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X, QuadraticRootBranchLocalization.oppositeRoot,
      laurentSlopeLinear]
    rfl

end FLT.Mazur.WeierstrassModificationX
