/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdentityIdeal

/-!
# Recovering original chart parameters in the full universal quotient

The chosen basis of the universal quotient has the original prescribed
polynomial values. Reading its structure constants returns the actual quotient
of the parameter ring, so no relations are lost by using quotient coordinates.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
set_option backward.isDefEq.respectTransparency false
variable (R I : Type*) [CommRing R] (d : ℕ) (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient quotient ring before interpreting chart coordinates. -/
local instance identityCoordinatesCoefficientsRing : CommRing (Coefficients R I d) :=
  inferInstance
/-- Cache the original chart quotient ring. -/
local instance identityCoordinatesChartRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the full universal polynomial quotient ring. -/
local instance identityCoordinatesQuotientRing :
    CommRing (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  inferInstance

/-- The universal quotient basis is given by the original prescribed polynomials. -/
theorem chartIdentityBasis_evaluation (i : Fin d) :
    MvPolynomial.aeval
        (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)) (w i) =
      chartIdentityBasis R I d w i :=
  quotientBasis_spec R I d w (ChartRing R I d w)
    (idealOfPoint R I d w (AlgHom.id R (ChartRing R I d w))) i

/-- Reading the full universal quotient recovers the original coefficient quotient map. -/
theorem chartIdentityBasis_readCoefficients (a : Coefficients R I d) :
    readCoefficients R I d (chartIdentityBasis R I d w)
        (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)) a =
      chartMap R I d w a := by
  have h := idealClassifyingMap_idealOfPoint R I d w (ChartRing R I d w)
    (AlgHom.id R (ChartRing R I d w))
  exact AlgHom.congr_fun h (chartMap R I d w a)

/-- The full universal quotient recovers each original multiplication parameter. -/
theorem chartIdentityBasis_mul (i j k : Fin d) :
    structureCoeff
        (A := MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w)
        (chartIdentityBasis R I d w) i j k =
      chartMap R I d w (mulCoeff R I d i j k) := by
  rw [← readCoefficients_mul R I d (chartIdentityBasis R I d w)
    (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)),
    chartIdentityBasis_readCoefficients]

/-- The full universal quotient recovers each original unit parameter. -/
theorem chartIdentityBasis_unit (k : Fin d) :
    structureUnit
        (A := MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w)
        (chartIdentityBasis R I d w) k =
      chartMap R I d w (unitCoeff R I d k) := by
  rw [← readCoefficients_unit R I d (chartIdentityBasis R I d w)
    (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)),
    chartIdentityBasis_readCoefficients]

/-- The full universal quotient recovers each original ambient generator parameter. -/
theorem chartIdentityBasis_generator (i : I) (k : Fin d) :
    (chartIdentityBasis R I d w).repr
        (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w) i) k =
      chartMap R I d w (generatorCoeff R I d i k) := by
  rw [← readCoefficients_generator R I d (chartIdentityBasis R I d w)
    (quotientGenerator I (ChartRing R I d w) (chartIdentityIdeal R I d w)),
    chartIdentityBasis_readCoefficients]

/-- A subalgebra containing all original parameters is the entire original chart ring. -/
theorem chart_subalgebra_eq_top_of_parameters (D : Subalgebra R (ChartRing R I d w))
    (hm : ∀ i j k, chartMap R I d w (mulCoeff R I d i j k) ∈ D)
    (hu : ∀ k, chartMap R I d w (unitCoeff R I d k) ∈ D)
    (hx : ∀ i k, chartMap R I d w (generatorCoeff R I d i k) ∈ D) : D = ⊤ := by
  let f : Parameters R I d →ₐ[R] ChartRing R I d w :=
    (Ideal.Quotient.mkₐ R (basisIdeal R I d w)).comp
      (Ideal.Quotient.mkₐ R (equationIdeal R I d))
  have hf (p : Parameters R I d) : f p ∈ D := by
    induction p using MvPolynomial.induction_on with
    | C r => exact D.algebraMap_mem r
    | add p q hp hq => simpa only [map_add] using D.add_mem hp hq
    | mul_X p z hp =>
      rw [map_mul]
      apply D.mul_mem hp
      cases z with
      | mul i j k => exact hm i j k
      | unit k => exact hu k
      | generator i k => exact hx i k
  apply top_unique
  intro z _
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact hf p

end FLT.Mazur.HilbertChart
