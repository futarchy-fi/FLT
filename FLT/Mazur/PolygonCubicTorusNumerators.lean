/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCanonicalDenominatorPolynomial

/-!
# All interpolation numerators on every component

The four Laurent terms retain both component indices. In particular the last
term survives at a self-incidence, and vanishes only after checking the indices.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Polynomial LaurentPolynomial
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonCubicSections
open PolygonPinching PolygonPowerNodeEndpoints
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)
  (a : Fin n → Kˣ)

/-- The numerator divided by the uniform interior section, on any component. -/
def interpolationLaurent (j i : Fin n) (k : Fin 3) : K[T;T⁻¹] :=
  LaurentPolynomial.C (cubicDelta K n i k 0 j) * LaurentPolynomial.T (-1) +
    LaurentPolynomial.C (cubicDelta K n i k 1 j) +
    LaurentPolynomial.C (cubicDelta K n i k 2 j) * LaurentPolynomial.T 1 +
    LaurentPolynomial.C (weight K n a 3 j *
      cubicDelta K n i k 0 ((finRotate n).symm j)) * LaurentPolynomial.T 2

/-- Every actual interpolation coordinate has the explicit four-term numerator. -/
lemma torusChartRingMap_interpolation (j i : Fin n) (k : Fin 3) :
    torusChartRingMap K n hn p q h a j
      (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n)
        ((cubicCoordinateEquiv.{u} n).symm (.inr ⟨(i, k)⟩))) =
      interpolationLaurent K n a j i k := by
  rw [torusChartRingMap_coordinate, torusRatio_eq, RingEquiv.symm_apply_apply]
  change Polynomial.toLaurent
    (((sectionEquiv K n hn p q h a 2
      (nodeSection K n hn p q h a _ _ _)).val j).val) * _ = _
  rw [nodeSection_polynomial]
  simp only [PolygonCubicInterpolation.cubic, ← Polynomial.C_mul_X_pow_eq_monomial,
    map_add, map_mul, Polynomial.toLaurent_C, Polynomial.toLaurent_X_pow,
    add_mul, mul_assoc, ← LaurentPolynomial.T_add, interpolationLaurent]
  simp

/-- The uniform interior coordinate is one in its own chart. -/
lemma torusChartRingMap_interior (i : Fin n) :
    torusChartRingMap K n hn p q h a i
      (ProjectiveSpace.coordinate K _ (interiorIndex.{u} n) (interiorIndex.{u} n)) = 1 := by
  simp [ProjectiveSpace.coordinate_self]

end FLT.Mazur.PolygonCubicSections
