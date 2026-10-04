/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSplitInterpolationEquations
public import FLT.Mazur.PolygonSplitLaurentNumerators
public import FLT.Mazur.PuncturedNodeRestrictionComparison

/-!
# Generator identities in the actual localized split-node ring

Cancellation takes place in the two punctured normalization localizations.
Faithful restriction then proves identities in A_s itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonSplitCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodeEqualizer PolygonNodeLocalization
open PolygonCubicSections PolygonPowerNodeEndpoints LocalizationJointRestriction
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ) (hn₂ : 2 ≤ n) (i : Fin n) (z : Spec (.of K))

/-- An interpolation coordinate in the exact chosen split-node localization. -/
def coordinate (l : Fin n) (k : Fin 3) :
    Localization.Away (splitDenominator K n hn p q h a hn₂ i z) :=
  affineCanonicalChartRingMap K n hn p q h a
    (splitDenominatorChart K n hn p q h a hn₂ i z)
    (splitDenominatorChart_range_subset K n hn p q h a hn₂ i z)
    (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} n)
      ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(l, k)⟩)))

local notation "s" => splitDenominator K n hn p q h a hn₂ i z
local notation "c" => coordinate K n hn p q h a hn₂ i z

private lemma mul_eq_of_cross {R : Type*} [CommRing R] {d r t b u v : R}
    (hd : IsUnit d) (hr : r * d = u) (hb : b * d = v) (ht : t * u = v) :
    t * r = b := by
  apply hd.mul_right_cancel
  rw [mul_assoc, hr, ht, hb]

private lemma weighted_mul_eq_of_cross {R : Type*} [CommRing R] {d r t b u v w : R}
    (hd : IsUnit d) (hr : r * d = u) (hb : b * d = v) (ht : t * u = w * v) :
    t * r = w * b := by
  apply hd.mul_right_cancel
  rw [mul_assoc, mul_assoc, hr, hb, ht]

/-- Multiplication by the first branch coordinate gives its linear interpolation coordinate. -/
lemma first_generator :
    algebraMap (A (R := K)) (Localization.Away s) x * c i 0 = c i 1 := by
  apply PuncturedNodeRestrictionComparison.split_ext s
  · rw [map_mul, restriction_algebraMap, leftMap_x]
    apply mul_eq_of_cross (split_left_denominator_isUnit K n hn p q h a hn₂ i z)
      (split_left_interpolation_equation K n hn p q h a hn₂ i z i 0)
      (split_left_interpolation_equation K n hn p q h a hn₂ i z i 1)
    rw [← map_mul, split_left_numerator_generator K n a hn₂ i]
  · rw [map_mul, restriction_algebraMap, rightMap_x, map_zero]
    apply mul_eq_of_cross (split_right_denominator_isUnit K n hn p q h a hn₂ i z)
      (split_right_interpolation_equation K n hn p q h a hn₂ i z i 0)
      (split_right_interpolation_equation K n hn p q h a hn₂ i z i 1)
    rw [interpolationLaurent_interior_other K n a i (finRotate n i)
      (split_successor_ne n hn₂ i) 1 (by decide), map_zero, zero_mul]

/-- The successor branch uses the quadratic coordinate and its exact matching weight. -/
lemma second_generator :
    algebraMap (A (R := K)) (Localization.Away s) y * c i 0 =
      algebraMap K (Localization.Away s) (weight K n a 3 (finRotate n i)) *
        c (finRotate n i) 2 := by
  have hs (f : A (R := K) →+* LaurentPolynomial K)
      (hf : ∀ r, f (algebraMap K (A (R := K)) r) = LaurentPolynomial.C r) (r : K) :
      restriction f s (algebraMap K (Localization.Away s) r) =
        algebraMap (LaurentPolynomial K) (Localization.Away (f s))
          (LaurentPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_apply K (A (R := K)) (Localization.Away s),
      restriction_algebraMap, hf]
  apply PuncturedNodeRestrictionComparison.split_ext s
  · rw [map_mul, map_mul, restriction_algebraMap, leftMap_y, map_zero, zero_mul]
    have hz : restriction leftMap s (c (finRotate n i) 2) = 0 := by
      apply (split_left_denominator_isUnit K n hn p q h a hn₂ i z).mul_right_cancel
      rw [zero_mul]
      exact (split_left_interpolation_equation K n hn p q h a hn₂ i z
        (finRotate n i) 2).trans (by
          rw [interpolationLaurent_interior_other K n a (finRotate n i) i
            (split_successor_ne n hn₂ i).symm 2 (by decide), map_zero])
    rw [hz, mul_zero]
  · rw [map_mul, map_mul, restriction_algebraMap, rightMap_y,
      hs rightMap (fun r ↦ by
        change (second (algebraMap K (A (R := K)) r)).toLaurent = _
        rw [AlgHom.commutes]
        exact Polynomial.toLaurent_C r)]
    apply weighted_mul_eq_of_cross
      (split_right_denominator_isUnit K n hn p q h a hn₂ i z)
      (split_right_interpolation_equation K n hn p q h a hn₂ i z i 0)
      (split_right_interpolation_equation K n hn p q h a hn₂ i z (finRotate n i) 2)
    change _ * (algebraMap (LaurentPolynomial K) _
      (LaurentPolynomial.invert (interpolationLaurent K n a (finRotate n i) i 0))) =
        _ * (algebraMap (LaurentPolynomial K) _
          (LaurentPolynomial.invert
            (interpolationLaurent K n a (finRotate n i) (finRotate n i) 2)))
    rw [← map_mul, ← map_mul, split_right_numerator_generator K n a hn₂ i]

end FLT.Mazur.PolygonSplitCubicCoordinates
