/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXAlgebra
public import FLT.Mazur.NilpotentQuadraticRoot

/-!
# Splitting the initial conic over the entire incidence line

The root is a polynomial in the original incidence coordinate. No incidence
coordinate is inverted, so the construction includes the complement of D(t).
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) (b3 b4 b6 : R)

/-- The original linear slope coefficient on the whole incidence line. -/
def polynomialSlopeLinear : R[X] := C W.a₁ + C b3 * X

/-- The original conic constant on the whole incidence line. -/
def polynomialSlopeConstant : R[X] := C W.a₂ + C b4 * X + C b6 * X ^ 2

variable (I : Ideal R) (hI : IsNilpotent I)

/-- The arithmetic ideal extended to the incidence polynomial algebra. -/
def polynomialArithmeticIdeal : Ideal R[X] := I.map C

include hI in
/-- Extending to the full incidence line preserves nilpotence. -/
theorem polynomialArithmeticIdeal_nilpotent : IsNilpotent (polynomialArithmeticIdeal I) := by
  obtain ⟨N, hN⟩ := hI
  refine ⟨N, ?_⟩
  rw [polynomialArithmeticIdeal, ← Ideal.map_pow, hN]
  exact Ideal.map_bot

variable (ha : IsUnit W.a₁) (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I)
  (h4 : b4 ∈ I) (h6 : b6 ∈ I)

include hI ha h3 in
/-- The original linear coefficient is invertible without removing t=0. -/
theorem polynomialSlopeLinear_unit : IsUnit (polynomialSlopeLinear W b3) := by
  have hm : C b3 * X ∈ polynomialArithmeticIdeal I :=
    (polynomialArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h3)
  exact (NilpotentQuadraticRoot.element_nilpotent _
    (polynomialArithmeticIdeal_nilpotent I hI) hm).isUnit_add_left_of_commute
      (ha.map C) (mul_comm _ _)

include h2 h4 h6 in
/-- The full conic constant lies in the extended arithmetic ideal. -/
theorem polynomialSlopeConstant_mem :
    polynomialSlopeConstant W b4 b6 ∈ polynomialArithmeticIdeal I := by
  exact (polynomialArithmeticIdeal I).add_mem
    ((polynomialArithmeticIdeal I).add_mem (Ideal.mem_map_of_mem _ h2)
      ((polynomialArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h4)))
    ((polynomialArithmeticIdeal I).mul_mem_right _ (Ideal.mem_map_of_mem _ h6))

/-- The original coefficients construct a root over the whole incidence line. -/
def polynomialSlopeRoot : R[X] :=
  NilpotentQuadraticRoot.root (polynomialArithmeticIdeal I)
    (polynomialArithmeticIdeal_nilpotent I hI) (polynomialSlopeLinear W b3)
    (polynomialSlopeConstant W b4 b6) (polynomialSlopeLinear_unit W b3 I hI ha h3)
    (polynomialSlopeConstant_mem W b4 b6 I h2 h4 h6)

/-- The polynomial root satisfies the full original conic equation. -/
theorem polynomialSlopeRoot_equation :
    polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6 ^ 2 +
      polynomialSlopeLinear W b3 * polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6 =
        polynomialSlopeConstant W b4 b6 := NilpotentQuadraticRoot.root_equation ..

/-- The polynomial root retains the small label at every incidence point. -/
theorem polynomialSlopeRoot_mem :
    polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6 ∈ polynomialArithmeticIdeal I :=
  NilpotentQuadraticRoot.root_mem ..

end FLT.Mazur.WeierstrassModificationX
