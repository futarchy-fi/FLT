/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassProjectiveAdditionChart
public import FLT.Mazur.WeierstrassScaledChartComparison

/-!
# Comparing a polynomial addition law with a homogeneous chart formula

On a polynomial output open, any proportional normalized chart formula has an
invertible proportionality factor. It therefore gives an actual output-overlap
map whose two restrictions are the given local laws.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (j k t u : Fin 3)
  (f : AdditionOutputOpen W j k t →ₐ[R] S) (a : Coordinate W u →ₐ[R] S)
  (q : S)
  (h : ∀ i, f (additionOutputRestriction W j k t
    (chartProductAdditionCoordinates W j k i)) = q * a (coord W u i))

include h in
/-- The homogeneous factor is invertible wherever the polynomial output is defined. -/
theorem polynomialComparison_factor_isUnit : IsUnit q := by
  have hu := (additionOutput_isUnit W j k t).map f
  rw [h t] at hu
  exact isUnit_of_mul_isUnit_left hu

include h in
/-- The comparison chart meets the selected polynomial output chart. -/
theorem polynomialComparison_coordinate_isUnit : IsUnit (a (coord W u t)) := by
  have hu := (additionOutput_isUnit W j k t).map f
  rw [h t] at hu
  exact isUnit_of_mul_isUnit_right hu

/-- Normalizing the polynomial formula also normalizes its homogeneous factor. -/
def polynomialComparisonScale : S := f (additionOutputInverse W j k t) * q

include h in
/-- The normalized proportionality factor is a unit. -/
theorem polynomialComparisonScale_isUnit :
    IsUnit (polynomialComparisonScale W j k t f q) :=
  ((Units.isUnit (additionOutput_isUnit W j k t).unit⁻¹).map f).mul
    (polynomialComparison_factor_isUnit W j k t u f a q h)

include h in
/-- Every normalized output coordinate has the same comparison factor. -/
theorem polynomialComparison_scaled (i : Fin 3) :
    f (projectiveAdditionChart W j k t (coord W t i)) =
      polynomialComparisonScale W j k t f q * a (coord W u i) := by
  rw [projectiveAdditionChart_coord, map_mul, h i, polynomialComparisonScale, mul_assoc]

/-- The comparison takes values in the actual overlap of the two output charts. -/
def polynomialComparisonLift : Overlap W t u →ₐ[R] S :=
  scaledChartLift W u t a (f.comp (projectiveAdditionChart W j k t))
    (polynomialComparisonScale W j k t f q)
    (polynomialComparisonScale_isUnit W j k t u f a q h)
    (polynomialComparison_scaled W j k t u f a q h)

/-- Restriction to the polynomial output chart recovers polynomial addition. -/
theorem polynomialComparisonLift_restriction :
    (polynomialComparisonLift W j k t u f a q h).comp (overlapRestriction W t u) =
      f.comp (projectiveAdditionChart W j k t) :=
  scaledChartLift_restriction ..

/-- Changing output charts recovers the compared normalized chart formula. -/
theorem polynomialComparisonLift_transition :
    (polynomialComparisonLift W j k t u f a q h).comp (transitionBase W t u) = a :=
  scaledChartLift_transition ..

end FLT.Mazur.WeierstrassIntegralChart
