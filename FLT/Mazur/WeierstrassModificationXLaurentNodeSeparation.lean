/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLaurentNodeDenominator
public import FLT.Mazur.WeierstrassModificationXOppositeNodeGeometry

/-!
# Each original initial Laurent boundary misses the opposite full node

The denominator of the wrong full node becomes nilpotent on the Laurent
boundary. This excludes the full opposite neighborhood at every arithmetic order.
-/

@[expose] public noncomputable section
open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (ha : IsUnit W.a₁) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "A" => Coordinate W s b3 b4 b6
local notation "B" => R[T;T⁻¹]
local notation "J" => laurentArithmeticIdeal I
local notation "E" => laurentBranchEvaluation W s b3 b4 b6 I hI ha hs h2 h3 h4 h6
variable (r : R[X]) (hrI : r ∈ I.map C)

include hrI in
/-- The wrong full-node denominator lies in the original extended nilpotent arithmetic ideal. -/
theorem laurentBranchEvaluation_oppositeDenominator_mem :
    E false (polynomialOppositeDenominator W s b3 b4 b6 r) ∈ J := by
  have he : E false (polynomialOppositeDenominator W s b3 b4 b6 r) =
      -nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 -
        r.eval₂ (algebraMap R B) (LaurentPolynomial.T (-1)) -
          algebraMap R B b3 * LaurentPolynomial.T (-1) := by
    rw [polynomialOppositeDenominator, map_add, map_neg, AlgHom.commutes,
      polynomialOppositeFactor, map_add, hom_polynomial_incidence]
    simp only [laurentBranchEvaluation, laurentSlopeEvaluation_v, laurentSlopeEvaluation_t]
    simp only [polynomialSlopeLinear, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_C, Polynomial.eval₂_X]
    simp only [laurentBranchSlope, Bool.false_eq_true, ↓reduceIte]
    ring
  rw [he]
  exact (J).sub_mem ((J).sub_mem ((J).neg_mem
    (nilpotentLaurentSlope_mem W s b3 b4 b6 I hI ha hs h2 h3 h4 h6))
    (NilpotentPolynomialInverse.eval₂_mem I (algebraMap R B) r hrI (LaurentPolynomial.T (-1))))
    ((J).mul_mem_right _ (Ideal.mem_map_of_mem _ h3))

include hrI in
/-- Reflection makes the first node denominator nilpotent on the opposite Laurent boundary. -/
theorem laurentBranchEvaluation_firstDenominator_mem :
    E true (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) ∈ J := by
  have h := DFunLike.congr_fun
    (laurentBranchEvaluation_reflection W s b3 b4 b6 I hI ha hs h2 h3 h4 h6)
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)
  change E false (initialReflection W s b3 b4 b6
    (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁)) = _ at h
  rw [initialReflection_denominator] at h
  rw [← h]
  exact laurentBranchEvaluation_oppositeDenominator_mem
    W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 r hrI

variable (hr : r ^ 2 + polynomialSlopeLinear W b3 * r = polynomialSlopeConstant W b4 b6)

/-- The complete small Laurent boundary does not meet the full opposite initial node. -/
theorem smallLaurent_oppositeNode_disjoint :
    Disjoint (Set.range (Spec.map (CommRingCat.ofHom (E false).toRingHom)))
      (Set.range (polynomialOppositeNodeChart W s b3 b4 b6 r hr I hI hrI h3)) := by
  rw [polynomialOppositeNodeChart_range]
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hz
  apply hz
  change E false (polynomialOppositeDenominator W s b3 b4 b6 r) ∈ z.asIdeal
  exact (nilpotent_iff_mem_prime.mp (NilpotentQuadraticRoot.element_nilpotent J
    (laurentArithmeticIdeal_nilpotent I hI)
    (laurentBranchEvaluation_oppositeDenominator_mem
      W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 r hrI))) z.asIdeal z.isPrime

/-- The complete opposite Laurent boundary does not meet the full first initial node. -/
theorem oppositeLaurent_firstNode_disjoint :
    Disjoint (Set.range (Spec.map (CommRingCat.ofHom (E true).toRingHom)))
      (Set.range (polynomialNodeChart W s b3 b4 b6 r hr I hI hrI h3)) := by
  rw [polynomialNodeChart_range]
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, rfl⟩ hz
  apply hz
  change E true (polynomialSmallFactor W s b3 b4 b6 r + algebraMap R A W.a₁) ∈ z.asIdeal
  exact (nilpotent_iff_mem_prime.mp (NilpotentQuadraticRoot.element_nilpotent J
    (laurentArithmeticIdeal_nilpotent I hI)
    (laurentBranchEvaluation_firstDenominator_mem
      W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 r hrI))) z.asIdeal z.isPrime

end FLT.Mazur.WeierstrassModificationX
