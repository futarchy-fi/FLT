/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartNoetherian
public import FLT.Mazur.PolynomialFlatQuotientPresentation

/-!
# Finitely presented ideals at arbitrary points of integer Hilbert charts

The test ring is arbitrary. Finite presentation of its full polynomial ideal
comes from a Noetherian universal chart and its free quotient, using arbitrary
coefficient change. No Noetherian hypothesis is imposed on the test ring.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
variable (R I : Type*) [CommRing R] [IsNoetherianRing R] [Finite I] (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable {S : Type*} [CommRing S] [Algebra R S]

/-- Cache the coefficient ring for ideal scalar extension. -/
local instance presentationCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for ideal scalar extension. -/
local instance presentationChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The entire ideal at any point of a Noetherian Hilbert chart is finitely presented. -/
theorem pointIdeal_finitePresentation (f : ChartRing R I d w →ₐ[R] S) :
    Module.FinitePresentation (MvPolynomial I S) (pointIdeal R I d w f) := by
  let _ := pointScalars R I d w f
  let _ := chartIdentityIdeal_finitePresentation R I d w
  have h := FCurve.polynomialIdeal_finitePresentation_map (S := S)
    (chartIdentityIdeal R I d w)
  change Module.FinitePresentation (MvPolynomial I S)
    ((chartIdentityIdeal R I d w).map (MvPolynomial.map f.toRingHom)) at h
  rwa [chartIdentityIdeal_map] at h

variable {A : Type*} [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]

/-- A polynomial quotient with an actual prescribed basis inherits ideal finite presentation. -/
theorem evaluation_ker_finitePresentation_of_basis
    (v : Module.Basis (Fin d) S A) (x : I → A)
    (hw : ∀ i, MvPolynomial.aeval x (w i) = v i) :
    Module.FinitePresentation (MvPolynomial I S)
      (RingHom.ker (MvPolynomial.aeval x : MvPolynomial I S →ₐ[S] A).toRingHom) := by
  have h := pointIdeal_finitePresentation R I d w (classifyingMap R I d v x w hw)
  rw [pointIdeal, pointReconstruction_ker] at h
  exact h

end FLT.Mazur.HilbertChart
