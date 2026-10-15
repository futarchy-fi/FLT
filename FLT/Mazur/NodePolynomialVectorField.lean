/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingDerivation
public import FLT.Mazur.PolygonSmoothingSpecialFiber

/-!
# Constructing original split-node vector fields from branch polynomials

Two polynomial vector fields vanishing at the branch origins define an
actual derivation on the original xy = 0 quotient. The two branch values
are constructed in its equalizer model and transported to the quotient;
the original tangent equation is proved from their disjoint branch support.
-/

@[expose] public noncomputable section
open scoped Polynomial
namespace FLT.Mazur.NodePolynomialVectorField
open PolygonSmoothing PolygonNodeEqualizer PolygonNodeLocalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] PolygonSmoothing.relationIdeal
variable {R : Type} [CommRing R]

/-- A polynomial vanishing at the origin is a node function supported on the first branch. -/
def leftValue (p : R[X]) (hp : p.coeff 0 = 0) : A (R := R) :=
  ⟨(p, 0), (mem_A _).mpr (by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero] using hp)⟩

/-- The corresponding function supported on the second branch. -/
def rightValue (p : R[X]) (hp : p.coeff 0 = 0) : A (R := R) :=
  ⟨(0, p), (mem_A _).mpr (by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_zero] using hp.symm)⟩

/-- The supported functions satisfy the node tangent equation exactly. -/
theorem values_relation (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    x * rightValue q hq + y * leftValue p hp = 0 := by
  apply Subtype.ext
  change (Polynomial.X * 0 + 0 * p, 0 * q + Polynomial.X * 0) = (0, 0)
  simp only [mul_zero, zero_mul, add_zero]

/-- The branch polynomials construct a derivation on the actual original node quotient. -/
def derivation (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    Derivation R (ChartRing (0 : R)) (ChartRing (0 : R)) :=
  derivationOfCoordinates (0 : R)
    ((specialFiberEquiv R).symm (leftValue p hp))
    ((specialFiberEquiv R).symm (rightValue q hq)) (by
      apply (specialFiberEquiv R).injective
      simp only [smul_eq_mul, map_add, map_mul, map_zero,
        specialFiberEquiv_left, specialFiberEquiv_right, AlgEquiv.apply_symm_apply]
      exact values_relation p q hp hq)

/-- The constructed derivation has precisely the prescribed first branch polynomial. -/
theorem derivation_left (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    specialFiberEquiv R (derivation p q hp hq (leftCoordinate (0 : R))) = leftValue p hp := by
  rw [derivation, derivationOfCoordinates_left, AlgEquiv.apply_symm_apply]

/-- The constructed derivation has precisely the prescribed second branch polynomial. -/
theorem derivation_right (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    specialFiberEquiv R (derivation p q hp hq (rightCoordinate (0 : R))) = rightValue q hq := by
  rw [derivation, derivationOfCoordinates_right, AlgEquiv.apply_symm_apply]

/-- Its actual first branch restriction retains every coefficient of the input polynomial. -/
theorem derivation_first (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    first (specialFiberEquiv R (derivation p q hp hq (leftCoordinate (0 : R)))) = p := by
  rw [derivation_left]
  rfl

/-- Its actual second branch restriction retains every coefficient of the other polynomial. -/
theorem derivation_second (p q : R[X]) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0) :
    second (specialFiberEquiv R (derivation p q hp hq (rightCoordinate (0 : R)))) = q := by
  rw [derivation_right]
  rfl

end FLT.Mazur.NodePolynomialVectorField
