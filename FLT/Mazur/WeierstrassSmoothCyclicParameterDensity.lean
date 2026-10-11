/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedCyclicSmoothParameter
public import FLT.Mazur.SurjectiveDominantEpi

/-!
# Density of the actual smooth affine parameter in the cyclic torus

The omitted smooth parameter is cut out by a nonzero Laurent polynomial.
Localization followed by the original reciprocal orientation is injective,
so its spectrum is dominant.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The normalized smooth Z coordinate does not vanish as a Laurent polynomial. -/
theorem splitNodalLaurentZ_ne_zero {K : Type u} [Field K] (a : Kˣ) :
    splitNodalLaurentZ a ≠ 0 := by
  have ht : (LaurentPolynomial.T (R := K) 1 - 1) ≠ 0 := by
    intro h
    have hh := congrArg (fun f : K[T;T⁻¹] => f.coeff 1) (sub_eq_zero.mp h)
    change (Finsupp.single (1 : ℤ) (1 : K)) 1 =
      (Finsupp.single (0 : ℤ) (1 : K)) 1 at hh
    norm_num [Finsupp.single_apply] at hh
  exact mul_ne_zero (pow_ne_zero _
    (mul_ne_zero ((a⁻¹).isUnit.map (algebraMap K K[T;T⁻¹])).ne_zero ht))
    ((LaurentPolynomial.isUnit_T (R := K) (-1)).ne_zero)

variable {R : Type u} [CommRing R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
open WeierstrassDividedDepth
local notation "K" => ResidueField R
local notation "L" => K[T;T⁻¹]
local notation "P" => SmoothYParameterRing D

/-- The original smooth affine localization retains every Laurent function. -/
theorem smoothYParameter_injective : Function.Injective (algebraMap L P) :=
  IsLocalization.injective P (powers_le_nonZeroDivisors_of_noZeroDivisors
    (splitNodalLaurentZ_ne_zero (WeierstrassDilatation.residueTangentUnit D)))


/-- Reciprocal cyclic orientation preserves injectivity of the original parameter. -/
theorem smoothYParameterCyclicAlgebra_injective :
    Function.Injective (smoothYParameterCyclicAlgebra D) :=
  (smoothYParameter_injective D).comp LaurentPolynomial.invert.injective

/-- The original cyclic smooth parameter is scheme-theoretically dense. -/
instance smoothYParameterCyclicMap_schematic :
    IsSchemeTheoreticallyDominant (smoothYParameterCyclicMap D) := by
  rw [← smoothYParameterCyclicAlgebra_spec]
  exact SurjectiveDominantEpi.spec_schematic _ (smoothYParameterCyclicAlgebra_injective D)

/-- The omitted affine smooth parameters do not affect the closure of the cyclic torus. -/
instance smoothYParameterCyclicMap_dominant : IsDominant (smoothYParameterCyclicMap D) := by
  rw [← smoothYParameterCyclicAlgebra_spec]
  let _ := SurjectiveDominantEpi.spec_schematic
    (smoothYParameterCyclicAlgebra D).toRingHom (smoothYParameterCyclicAlgebra_injective D)
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
