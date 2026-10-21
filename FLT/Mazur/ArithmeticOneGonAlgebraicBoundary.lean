/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonAlgebraicFamily
public import FLT.Mazur.ArithmeticOneGonBoundaryFiber

/-!
# Boundary and smooth equations in the algebraic one-gon family

The zero-parameter fiber is the original pinched one-gon as a full generalized
curve in every characteristic. The complementary parameter fibers are elliptic.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonParameter
open OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

/-- Parameter zero is retained in every residue characteristic. -/
theorem zero_factor_isUnit : IsUnit (1 + 432 * (0 : K)) := by simp

/-- The algebraic degeneration's zero fiber is the original full pinched one-gon. -/
irreducible_def originalBoundaryIso :
    PolygonGeneralizedCurve.curve K 1 Nat.zero_lt_one
      (OneGonNormalization.normalizationOver K) (OneGonNormalization.nodes K)
      (OneGonGlobalPushout.isPushout K Nat.zero_lt_one) ≅
        universalCurve.baseChange (parameterMap (0 : K) (zero_factor_isUnit K)) := by
  letI : Algebra ParameterRing K := (specialize (0 : K) (zero_factor_isUnit K)).toAlgebra
  exact ArithmeticOneGonBoundaryFiber.curveIso K parameter factor_isUnit
    (specialize_parameter (0 : K) (zero_factor_isUnit K))

/-- Every field-valued zero-parameter map is exactly the original boundary classifying map. -/
theorem zero_specialization_unique (f : ParameterRing →+* K) (hf : f parameter = 0) :
    f = specialize (0 : K) (zero_factor_isUnit K) := by
  apply hom_ext
  rw [specialize_parameter, hf]

/-- The actual specialized discriminant is nonzero precisely off the parameter-zero locus. -/
theorem field_discriminant_ne_zero_iff (f : ParameterRing →+* K) :
    ((equation parameter).map f).Δ ≠ 0 ↔ f parameter ≠ 0 := by
  rw [equation_map, equation_discriminant]
  exact ⟨fun h hz ↦ h (by rw [hz, neg_zero, zero_mul]),
    fun h ↦ mul_ne_zero (neg_ne_zero.mpr h) (hom_factor_isUnit f).ne_zero⟩

/-- Every nonzero field-valued parameter gives an elliptic equation, in any characteristic. -/
theorem fieldEquation_isElliptic (f : ParameterRing →+* K) (hf : f parameter ≠ 0) :
    ((equation parameter).map f).IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr ((field_discriminant_ne_zero_iff K f).mpr hf)⟩

end FLT.Mazur.ArithmeticOneGonParameter
