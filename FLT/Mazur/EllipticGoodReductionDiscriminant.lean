/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction

/-!
# Unit discriminant of the supplied good-reduction equation

Mathlib's good-reduction predicate concerns the supplied minimal equation.
For an equation already over the DVR, its discriminant is therefore a unit;
no additional variable change or replacement of the original points is needed.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing IsDiscreteValuationRing
open IsDedekindDomain.HeightOneSpectrum

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K] (W : WeierstrassCurve R)

/-- Good reduction of an already integral equation makes its discriminant a unit. -/
theorem isUnit_discriminant_of_hasGoodReduction
    [(W.map (algebraMap R K)).HasGoodReduction R] : IsUnit W.Δ := by
  have h := HasGoodReduction.goodReduction (R := R) (W := W.map (algebraMap R K))
  rw [map_Δ, valuation_eq_one_iff_notMem] at h
  exact (notMem_maximalIdeal).mp h

end FLT.Mazur
