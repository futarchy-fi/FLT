/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPuncturedCanonicalEquations
public import FLT.Mazur.PolygonCubicTorusNumerators

/-!
# Explicit interpolation equations on the actual punctured rings

Substitute both the canonical cubic denominator and each interpolation numerator.
The interior coordinate proves that the denominator is a unit in these rings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonNodePresentation LocalizationJointRestriction
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (x : Spec (.of K))

/-- The left branch with both actual polynomials substituted. -/
lemma split_left_interpolation_equation (l : Fin n) (k : Fin 3) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let j := splitDenominatorChart K n hn p q h a hn₂ i x
    let c := affineCanonicalChartRingMap K n hn p q h a j
      (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x)
    let g := algebraMap (LaurentPolynomial K) (Localization.Away (leftMap s))
    restriction leftMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n)
          ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩)))) *
      g ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a i : K)) ^ 3 *
        LaurentPolynomial.T (-1)) =
      g (interpolationLaurent K n a i l k) := by
  have he := split_left_canonical_equation K n hn p q h a hn₂ i x
    ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩))
  dsimp only at he ⊢
  rwa [torusChartRingMap_canonical, torusChartRingMap_interpolation] at he

/-- The left denominator is a unit, witnessed by the actual interior ratio. -/
lemma split_left_denominator_isUnit :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let g := algebraMap (LaurentPolynomial K) (Localization.Away (leftMap s))
    IsUnit (g ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a i : K)) ^ 3 *
        LaurentPolynomial.T (-1))) := by
  have he := split_left_canonical_equation K n hn p q h a hn₂ i x (interiorIndex.{u} n)
  dsimp only at he ⊢
  rw [torusChartRingMap_canonical, torusChartRingMap_interior, map_one] at he
  exact IsUnit.of_mul_eq_one_right _ he

/-- The right branch with both actual polynomials substituted. -/
lemma split_right_interpolation_equation (l : Fin n) (k : Fin 3) :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let j := splitDenominatorChart K n hn p q h a hn₂ i x
    let c := affineCanonicalChartRingMap K n hn p q h a j
      (splitDenominatorChart_range_subset K n hn p q h a hn₂ i x)
    let g := (algebraMap (LaurentPolynomial K) (Localization.Away (rightMap s))).comp
      (LaurentPolynomial.invert (R := K)).toRingHom
    restriction rightMap s
        (c (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n)
          ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩)))) *
      g ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a (finRotate n i) : K)) ^ 3 *
        LaurentPolynomial.T (-1)) =
      g (interpolationLaurent K n a (finRotate n i) l k) := by
  have he := split_right_canonical_equation K n hn p q h a hn₂ i x
    ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩))
  dsimp only at he ⊢
  rwa [torusChartRingMap_canonical, torusChartRingMap_interpolation] at he

/-- The right denominator is a unit, witnessed by the actual interior ratio. -/
lemma split_right_denominator_isUnit :
    let s := splitDenominator K n hn p q h a hn₂ i x
    let g := (algebraMap (LaurentPolynomial K) (Localization.Away (rightMap s))).comp
      (LaurentPolynomial.invert (R := K)).toRingHom
    IsUnit (g ((LaurentPolynomial.T 1 - LaurentPolynomial.C (a (finRotate n i) : K)) ^ 3 *
        LaurentPolynomial.T (-1))) := by
  have he := split_right_canonical_equation K n hn p q h a hn₂ i x (interiorIndex.{u} n)
  dsimp only at he ⊢
  rw [torusChartRingMap_canonical, torusChartRingMap_interior, map_one] at he
  exact IsUnit.of_mul_eq_one_right _ he

end FLT.Mazur.PolygonCubicSections
