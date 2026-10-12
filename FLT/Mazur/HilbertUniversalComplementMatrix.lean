/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertMonomialReindexedAmbient
public import FLT.Mazur.HilbertReindexedCoordinateRing
public import FLT.Mazur.GrassmannianNormalizedAmbientCoordinates

/-!
# The complementary matrix of the original universal Hilbert quotient

The closed coordinate map reads exactly the normalized quotient map in the
original ambient decomposition. This computes the entire map, including its
selected columns, rather than only its values on complementary generators.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
open GrassmannianChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ)
  (m : Fin d → BoundedHilbertMonomials I d)
  {κ : Type u} [Fintype κ] (hm : Function.Injective m)
  (e : HilbertComplementMonomials I d m ≃ κ)
local notation "w" => (fun a ↦ MvPolynomial.monomial (Subtype.val (m a)) (1 : R))
local notation "C" => ChartRing R I d w
local notation "J" => chartIdentityIdeal R I d w
local notation "v" => chartIdentityBasis R I d w
local notation "c" => hilbertReindexedAmbient R I d m hm e
local notation "q" => hilbertAmbientCoordinates R C I J d v

/-- Cache the coefficient ring for the original chart quotient. -/
local instance universalComplementCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the original chart ring. -/
local instance universalComplementChartRing : CommRing C := inferInstance
/-- Cache the original universal polynomial quotient. -/
local instance universalComplementQuotientRing : CommRing (MvPolynomial I C ⧸ J) :=
  inferInstance

/-- The original universal quotient basis consists of the selected monomials. -/
theorem chartIdentityBasis_monomial (j : Fin d) :
    Ideal.Quotient.mk J (MvPolynomial.monomial (m j).val 1) = v j := by
  simpa only [quotientGenerator_evaluation, MvPolynomial.map_monomial, map_one] using
    chartIdentityBasis_evaluation R I d w j

/-- The universal quotient coordinates are the identity on the original selected summand. -/
theorem chartIdentityCoordinates_selected :
    (q).comp (ambientChartSelected (ambientChartBaseChange C c)) = LinearMap.id :=
  hilbertReindexedAmbient_selected_coordinates R I d m C hm e J v
    (chartIdentityBasis_monomial R I d m)

/-- The polynomial coordinate map reads precisely the full complementary linear map. -/
theorem chartIdentityCoordinates_complement :
    let _ := Classical.decEq κ
    (q).comp (ambientChartComplement (ambientChartBaseChange C c)) =
      Matrix.toLin' (matrixPolynomialHomEquiv R C κ d
        (chartReindexedCoordinateMap R I d m e)) := by
  classical
  apply LinearMap.toMatrix'.injective
  rw [LinearMap.toMatrix'_toLin']
  ext k j
  change q (ambientChartComplement (ambientChartBaseChange C c) (Pi.single j 1)) k = _
  change q (ambientChartComplement (ambientChartBaseChange C c) (Pi.basisFun C κ j)) k = _
  rw [hilbertReindexedAmbient_complement]
  change _ = chartReindexedCoordinateMap R I d m e (MvPolynomial.X (k, j))
  rw [chartReindexedCoordinateMap_X]
  exact (chartBoundedCoordinate_ambient R I d w k (e.symm j).val).symm

/-- The complete original ambient evaluation is the split evaluation of the chart matrix. -/
theorem chartIdentityCoordinates_factor :
    let _ := Classical.decEq κ
    (q).comp (ambientChartBaseChange C c).toLinearMap =
      splitChartEvaluation (Matrix.toLin' (matrixPolynomialHomEquiv R C κ d
        (chartReindexedCoordinateMap R I d m e))) := by
  classical
  rw [normalizedAmbientCoordinates_factor _ _
    (chartIdentityCoordinates_selected R I d m hm e),
    chartIdentityCoordinates_complement]

end FLT.Mazur.HilbertChart
