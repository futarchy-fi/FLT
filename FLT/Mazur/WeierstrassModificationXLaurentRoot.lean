/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXLocalization
public import FLT.Mazur.NilpotentQuadraticRoot
public import FLT.Mazur.QuadraticRootOppositeBranch
public import FLT.Mazur.LaurentUnitPoints

/-!
# Constructed Laurent roots of the original initial equation

On the original incidence open, t is the inverse Laurent parameter.
The original coefficients determine the small root over every nilpotent base.
-/

@[expose] public noncomputable section
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (s b3 b4 b6 : R)

/-- The linear coefficient of the original initial slope on its incidence open. -/
def laurentSlopeLinear : R[T;T⁻¹] :=
  LaurentPolynomial.C W.a₁ + LaurentPolynomial.C b3 * LaurentPolynomial.T (-1)

/-- The constant side retains the original scale and all initial divided coefficients. -/
def laurentSlopeConstant : R[T;T⁻¹] :=
  LaurentPolynomial.C s * LaurentPolynomial.T 1 + LaurentPolynomial.C W.a₂ +
    LaurentPolynomial.C b4 * LaurentPolynomial.T (-1) +
      LaurentPolynomial.C b6 * LaurentPolynomial.T (-1) ^ 2

variable (I : Ideal R) (hI : IsNilpotent I)

/-- The original arithmetic ideal extended to the full Laurent algebra. -/
def laurentArithmeticIdeal : Ideal R[T;T⁻¹] := I.map (algebraMap R R[T;T⁻¹])

include hI in
/-- The initial Laurent arithmetic ideal remains nilpotent. -/
theorem laurentArithmeticIdeal_nilpotent : IsNilpotent (laurentArithmeticIdeal I) := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  rw [laurentArithmeticIdeal, ← Ideal.map_pow, hN]
  exact Ideal.map_bot

variable (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

include hI ha h3 in
/-- The original initial Laurent linear coefficient is a unit. -/
theorem laurentSlopeLinear_unit : IsUnit (laurentSlopeLinear W b3) := by
  have hm : LaurentPolynomial.C b3 * LaurentPolynomial.T (-1) ∈
      laurentArithmeticIdeal I :=
    (laurentArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  exact (NilpotentQuadraticRoot.element_nilpotent _
    (laurentArithmeticIdeal_nilpotent I hI) hm).isUnit_add_left_of_commute
      (ha.map LaurentPolynomial.C) (mul_comm _ _)

include hs h2 h4 h6 in
/-- All original constant terms vanish modulo the specified arithmetic ideal. -/
theorem laurentSlopeConstant_mem :
    laurentSlopeConstant W s b4 b6 ∈ laurentArithmeticIdeal I := by
  apply (laurentArithmeticIdeal I).add_mem
  · apply (laurentArithmeticIdeal I).add_mem
    · exact (laurentArithmeticIdeal I).add_mem
        ((laurentArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ hs))
        (Ideal.mem_map_of_mem _ h2)
    · exact (laurentArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h4)
  · exact (laurentArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h6)

/-- The original initial coefficients construct the small Laurent slope. -/
def nilpotentLaurentSlope : R[T;T⁻¹] :=
  NilpotentQuadraticRoot.root (laurentArithmeticIdeal I)
    (laurentArithmeticIdeal_nilpotent I hI) (laurentSlopeLinear W b3)
    (laurentSlopeConstant W s b4 b6) (laurentSlopeLinear_unit W b3 I hI ha h3)
    (laurentSlopeConstant_mem W s b4 b6 I hs h2 h4 h6)

/-- The constructed initial Laurent slope solves the full original quadratic. -/
theorem nilpotentLaurentSlope_equation :
    nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 ^ 2 +
      laurentSlopeLinear W b3 *
        nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 =
      laurentSlopeConstant W s b4 b6 := NilpotentQuadraticRoot.root_equation ..

/-- The initial slope retains its specified zero label modulo the arithmetic ideal. -/
theorem nilpotentLaurentSlope_mem :
    nilpotentLaurentSlope W s b3 b4 b6 I hI ha hs h2 h3 h4 h6 ∈
      laurentArithmeticIdeal I := NilpotentQuadraticRoot.root_mem ..

end FLT.Mazur.WeierstrassModificationX
