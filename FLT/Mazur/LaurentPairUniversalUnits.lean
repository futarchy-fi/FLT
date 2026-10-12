/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineUniversalLaurentEvaluation
public import FLT.Mazur.LaurentUnitPointNaturality

/-!
# Independent universal units and their specializations

The two Laurent variables represent arbitrary pairs of units, including points
in nonreduced algebras. Constants and both inverse coordinates remain explicit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.ProjectiveLineUniversalAction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (K : Type u) [Field K]

/-- The coefficient Laurent variable is the first independent unit. -/
def laurentPairFirstUnit : K[T;T⁻¹][T;T⁻¹]ˣ :=
  Units.map (LaurentPolynomial.C : K[T;T⁻¹] →+* K[T;T⁻¹][T;T⁻¹]).toMonoidHom
    (PolygonUniversalScaling.u (R := K))

/-- The outer Laurent variable is the second independent unit. -/
def laurentPairSecondUnit : K[T;T⁻¹][T;T⁻¹]ˣ :=
  PolygonUniversalScaling.u

variable {K} {A : Type u} [CommRing A] [Algebra K A] (q r : Aˣ)

/-- Evaluation retains the first independent unit. -/
theorem laurentPairEvaluation_firstUnit :
    Units.map (laurentPairEvaluation (K := K) q r).toMonoidHom
      (laurentPairFirstUnit K) = q := by
  apply Units.ext
  change LaurentPolynomial.eval₂ _ r (LaurentPolynomial.C _) = _
  simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

/-- Evaluation retains the second independent unit. -/
theorem laurentPairEvaluation_secondUnit :
    Units.map (laurentPairEvaluation (K := K) q r).toMonoidHom
      (laurentPairSecondUnit K) = r := by
  apply Units.ext
  change LaurentPolynomial.eval₂ _ r
    (↑(PolygonUniversalScaling.u (R := K[T;T⁻¹])) : K[T;T⁻¹][T;T⁻¹]) = _
  simp [PolygonUniversalScaling.u, PolygonChartScaling.coordinateUnit]

/-- Coefficient units specialize along the prescribed algebra map. -/
theorem laurentPairEvaluation_constantUnit (a : Kˣ) :
    Units.map (laurentPairEvaluation (K := K) q r).toMonoidHom
      (Units.map (algebraMap K K[T;T⁻¹][T;T⁻¹]) a) =
        Units.map (algebraMap K A) a := by
  apply Units.ext
  exact (laurentPairEvaluation (K := K) q r).commutes (a : K)

end FLT.Mazur.ProjectiveLineUniversalAction
