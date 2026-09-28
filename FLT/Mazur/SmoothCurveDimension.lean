/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleCoordinate
public import FLT.Mazur.EtaleDimGe
public import FLT.Mazur.EtaleDimLe
public import FLT.Mazur.SmoothDimension

/-!
# Dimension of smooth curves

A nonzero standard-smooth algebra of relative dimension one over a field has
an étale polynomial coordinate. The upper and lower dimension bounds for this
coordinate show that its Krull dimension is one. Applying this to affine charts
discharges the smooth curve dimension contract.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

/-- A nonzero standard-smooth algebra of relative dimension one has dimension one. -/
theorem ringKrullDim_eq_one_of_standardSmooth
    (K A : Type*) [Field K] [CommRing A] [Nontrivial A] [Algebra K A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 K A] : ringKrullDim A = 1 := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := 1) (R := K) (S := A)
  have he := P.coordinateHom_etale hP
  algebraize [(P.coordinateHom hP).toRingHom]
  exact le_antisymm (ringKrullDim_le_one_of_etale_polynomial K A)
    (oneLeRingKrullDimOfEtalePolynomial K A)

/-- The dimension statement for a standard-smooth ring homomorphism from a field. -/
theorem ringKrullDim_eq_one_of_isStandardSmoothOfRelativeDimension
    (K A : Type*) [Field K] [CommRing A] [Nontrivial A]
    (g : K →+* A) (hg : g.IsStandardSmoothOfRelativeDimension 1) :
    ringKrullDim A = 1 := by
  algebraize [g]
  exact ringKrullDim_eq_one_of_standardSmooth K A

/-- Every nonempty smooth relative-dimension-one scheme over a field has dimension one. -/
theorem smoothCurveDimension {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) : SmoothCurveDimension f := by
  apply smoothCurveDimension_of_standardSmooth_dimension K
  intro A _ _ g hg
  exact ringKrullDim_eq_one_of_isStandardSmoothOfRelativeDimension K A g hg

end FLT.Mazur.FCurve
