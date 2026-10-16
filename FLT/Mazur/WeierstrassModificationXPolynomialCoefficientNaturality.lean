/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXPolynomialRoot

/-!
# Original polynomial tangent roots commute with coefficient change

Uniqueness preserves the complete conic root on the incidence line under
every coefficient map preserving the arithmetic ideals.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassModificationX
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (b3 b4 b6 : R)
local notation "F" => Polynomial.mapRingHom f
local notation "U" => W.map f

/-- The polynomial linear coefficient retains all original coefficients. -/
theorem polynomialSlopeLinear_coefficient :
    F (polynomialSlopeLinear W b3) = polynomialSlopeLinear U (f b3) := by
  simp only [Polynomial.coe_mapRingHom, polynomialSlopeLinear, map_add, map_mul, Polynomial.map_C,
    Polynomial.map_X, WeierstrassCurve.map_a₁]

/-- The polynomial constant retains all divided cubic terms. -/
theorem polynomialSlopeConstant_coefficient :
    F (polynomialSlopeConstant W b4 b6) =
      polynomialSlopeConstant U (f b4) (f b6) := by
  simp only [Polynomial.coe_mapRingHom, polynomialSlopeConstant, map_add, map_mul, map_pow,
    Polynomial.map_C,
    Polynomial.map_X, WeierstrassCurve.map_a₂]

variable (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)

include hf in
/-- Arithmetic ideal preservation extends to the complete incidence polynomial algebra. -/
theorem polynomialArithmeticIdeal_coefficient :
    polynomialArithmeticIdeal I ≤ (polynomialArithmeticIdeal J).comap F := by
  rw [polynomialArithmeticIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  change Polynomial.map f (C x) ∈ polynomialArithmeticIdeal J
  rw [Polynomial.map_C]
  exact Ideal.mem_map_of_mem (C : S →+* S[X]) (hf hx)

variable (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (ha : IsUnit W.a₁) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)

/-- The constructed polynomial root, including every correction, is natural in coefficients. -/
theorem polynomialSlopeRoot_coefficient :
    F (polynomialSlopeRoot W b3 b4 b6 I hI ha h2 h3 h4 h6) =
      polynomialSlopeRoot U (f b3) (f b4) (f b6) J hJ
        (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6) := by
  apply NilpotentQuadraticRoot.root_unique (polynomialArithmeticIdeal J)
    (polynomialArithmeticIdeal_nilpotent J hJ) (polynomialSlopeLinear U (f b3))
    (polynomialSlopeConstant U (f b4) (f b6))
    (polynomialSlopeLinear_unit U (f b3) J hJ (ha.map f) (hf h3))
  · exact polynomialArithmeticIdeal_coefficient f I J hf
      (polynomialSlopeRoot_mem W b3 b4 b6 I hI ha h2 h3 h4 h6)
  · exact polynomialSlopeRoot_mem U (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)
  · have he := congrArg F
      (polynomialSlopeRoot_equation W b3 b4 b6 I hI ha h2 h3 h4 h6)
    simpa only [map_add, map_mul, map_pow, polynomialSlopeLinear_coefficient,
      polynomialSlopeConstant_coefficient] using he
  · exact polynomialSlopeRoot_equation U (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf h2) (hf h3) (hf h4) (hf h6)

end FLT.Mazur.WeierstrassModificationX
