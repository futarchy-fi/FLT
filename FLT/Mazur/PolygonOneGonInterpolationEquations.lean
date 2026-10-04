/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPuncturedCanonicalEquations
public import FLT.Mazur.PolygonCubicTorusNumerators

/-!
# The canonical cubic equations after the one-gon Möbius substitution

These are equations in the actual localization of K[t,1/(t(t-1))].
The node numerator keeps its cubic self-incidence contribution.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.OneGonTransition
variable (K : Type u) [Field K]

/-- The inverse Laurent coordinate undergoes the inverse Möbius substitution. -/
lemma overlapMap_inverse :
    overlapMap K (LaurentPolynomial.T (-1)) = (↑(mobius K)⁻¹ : puncture K) := by
  apply (mobius K).isUnit.mul_left_cancel
  rw [← overlapMap_T, ← map_mul, ← LaurentPolynomial.T_add]
  simp

/-- The quadratic Laurent coordinate becomes the square of the Möbius coordinate. -/
lemma overlapMap_square :
    overlapMap K (LaurentPolynomial.T 2) = (mobius K : puncture K) ^ 2 := by
  rw [show (LaurentPolynomial.T 2 : LaurentPolynomial K) =
    LaurentPolynomial.T 1 * LaurentPolynomial.T 1 from LaurentPolynomial.T_add 1 1]
  rw [map_mul, overlapMap_T, pow_two]

end OneGonTransition
namespace PolygonCubicSections
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation LocalizationJointRestriction
open PolygonPowerNodeEndpoints OneGonTransition
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K))

/-- The self-incidence numerator, with all three interpolation coefficients explicit. -/
def oneInterpolationNumerator (i : Fin 1) (k : Fin 3) : puncture K :=
  if k = 0 then (↑(mobius K)⁻¹ : puncture K) +
    algebraMap K (puncture K) (weight K 1 a 3 i) * (mobius K : puncture K) ^ 2
  else if k = 1 then 1 else (mobius K : puncture K)

/-- The actual overlap map computes the indicated Möbius expression. -/
lemma one_interpolation_substitution (i : Fin 1) (k : Fin 3) :
    overlapMap K (interpolationLaurent K 1 a i i k) =
      oneInterpolationNumerator K a i k := by
  fin_cases k <;>
    simp [interpolationLaurent, cubicDelta, oneInterpolationNumerator,
      overlapMap_inverse, overlapMap_square, overlapMap_C]

/-- The cubic denominator after the actual Möbius substitution. -/
def oneCanonicalDenominator (i : Fin 1) : puncture K :=
  ((mobius K : puncture K) - algebraMap K (puncture K) (a i : K)) ^ 3 *
    (↑(mobius K)⁻¹ : puncture K)

/-- Substitution of both the canonical denominator and the self-incidence numerator. -/
lemma one_interpolation_equation (i : Fin 1) (k : Fin 3) :
    let s := oneDenominator K hn p q h a x
    let j := oneDenominatorChart K hn p q h a x
    let c := affineCanonicalChartRingMap K 1 hn p q h a j
      (oneDenominatorChart_range_subset K hn p q h a x)
    let g := algebraMap (puncture K) (Localization.Away (bPunctureMap s))
    restriction bPunctureMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} 1)
          ((cubicCoordinateEquiv.{u} 1).symm (.inr ⟨(i, k)⟩)))) *
      g (oneCanonicalDenominator K a i) = g (oneInterpolationNumerator K a i k) := by
  have he := one_canonical_equation K hn p q h a x i
    ((cubicCoordinateEquiv.{u} 1).symm (.inr ⟨(i, k)⟩))
  dsimp only at he ⊢
  rw [torusChartRingMap_canonical, torusChartRingMap_interpolation] at he
  simpa only [RingHom.comp_apply, map_mul, map_pow, map_sub, overlapMap_T,
    overlapMap_C, overlapMap_inverse, one_interpolation_substitution,
    oneCanonicalDenominator] using he

/-- The actual interior ratio supplies the inverse of the substituted denominator. -/
lemma one_canonical_denominator_isUnit (i : Fin 1) :
    let s := oneDenominator K hn p q h a x
    IsUnit (algebraMap (puncture K) (Localization.Away (bPunctureMap s))
      (oneCanonicalDenominator K a i)) := by
  have he := one_canonical_equation K hn p q h a x i (interiorIndex.{u} 1)
  dsimp only at he ⊢
  rw [torusChartRingMap_canonical, torusChartRingMap_interior, map_one] at he
  apply IsUnit.of_mul_eq_one_right _
  simpa only [RingHom.comp_apply, map_mul, map_pow, map_sub, overlapMap_T,
    overlapMap_C, overlapMap_inverse, oneCanonicalDenominator] using he

end FLT.Mazur.PolygonCubicSections
