/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundedCoordinateGeneration
public import FLT.Mazur.HilbertIdentityQuotientCoordinates
public import FLT.Mazur.HilbertBoundedQuotientCoordinates

/-!
# Surjective bounded-coordinate maps onto original Hilbert chart rings

The polynomial algebra of all bounded quotient coordinates maps onto the
original chart ring. The proof recovers each original structure parameter;
the target retains every ring-law and prescribed-basis equation.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
universe u
variable (R I : Type u) [CommRing R] (d : ℕ) (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient quotient for bounded coordinate synthesis. -/
local instance boundedCoordinatesCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the original chart ring. -/
local instance boundedCoordinatesChartRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the full universal quotient ring. -/
local instance boundedCoordinatesQuotientRing :
    CommRing (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  inferInstance

/-- The affine coordinate algebra for all columns in the degree d+1 truncation. -/
abbrev BoundedCoordinateRing := MvPolynomial (Fin d × BoundedHilbertMonomials I (d + 1)) R

/-- Read a bounded monomial column in the full original universal quotient. -/
def chartBoundedCoordinate (k : Fin d) (m : BoundedHilbertMonomials I (d + 1)) :
    ChartRing R I d w :=
  (chartIdentityBasis R I d w).repr
    (MvPolynomial.aeval
      (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w))
      (MvPolynomial.monomial m.val (1 : R))) k

/-- The original bounded-coordinate polynomial parameter map. -/
def chartBoundedCoordinateMap : BoundedCoordinateRing R I d →ₐ[R] ChartRing R I d w :=
  MvPolynomial.aeval fun km ↦ chartBoundedCoordinate R I d w km.1 km.2

/-- Each polynomial coordinate is evaluated at its actual universal quotient column. -/
theorem chartBoundedCoordinateMap_X (k : Fin d)
    (m : BoundedHilbertMonomials I (d + 1)) :
    chartBoundedCoordinateMap R I d w (MvPolynomial.X (k, m)) =
      chartBoundedCoordinate R I d w k m := MvPolynomial.aeval_X _ _

/-- These are precisely the bounded Grassmannian evaluation coordinates of the full family. -/
theorem chartBoundedCoordinate_ambient (k : Fin d)
    (m : BoundedHilbertMonomials I (d + 1)) :
    chartBoundedCoordinate R I d w k m =
      hilbertAmbientCoordinates R (ChartRing R I d w) I (chartIdentityIdeal R I d w) d
        (chartIdentityBasis R I d w)
        (1 ⊗ₜ[R] boundedPolynomialBasis R I (d + 1) m) k := by
  rw [hilbertAmbientCoordinates_monomial]
  simp only [chartBoundedCoordinate, quotientGenerator_evaluation,
    MvPolynomial.map_monomial, map_one, Module.Basis.equivFun_apply]

/-- Bounded quotient coordinates generate the entire original Hilbert chart ring. -/
theorem chartBoundedCoordinateMap_surjective (hw : ∀ i, (w i).totalDegree ≤ d) :
    Function.Surjective (chartBoundedCoordinateMap R I d w) := by
  let D := (chartBoundedCoordinateMap R I d w).range
  let v := chartIdentityBasis R I d w
  let x := quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)
  have hm (m : BoundedHilbertMonomials I (d + 1)) (k : Fin d) :
      v.repr (MvPolynomial.aeval x (MvPolynomial.monomial m.val (1 : R))) k ∈ D :=
    ⟨MvPolynomial.X (k, m), chartBoundedCoordinateMap_X R I d w k m⟩
  have ht : D = ⊤ := by
    apply chart_subalgebra_eq_top_of_parameters
    · intro i j k
      rw [← chartIdentityBasis_mul]
      exact bounded_structure_coordinates_mem
        (A := MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) v D x hm w hw
        (chartIdentityBasis_evaluation R I d w) i j k
    · intro k
      rw [← chartIdentityBasis_unit]
      exact bounded_unit_coordinates_mem
        (A := MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) v D x hm k
    · intro i k
      rw [← chartIdentityBasis_generator]
      exact bounded_generator_coordinates_mem
        (A := MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) v D x hm i k
  intro z
  have hz : z ∈ D := by rw [ht]; trivial
  exact hz

end FLT.Mazur.HilbertChart
