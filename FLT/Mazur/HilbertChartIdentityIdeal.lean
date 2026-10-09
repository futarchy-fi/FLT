/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartClassificationNaturality
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# The actual universal ideal on a Hilbert chart

The identity chart parameter defines the universal polynomial ideal. Its
quotient has the prescribed basis, and extension along any parameter recovers
the actual ideal of that parameter.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.HilbertChart

variable (R : Type*) [CommRing R] (I : Type*) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for quotient inference. -/
local instance identityCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for quotient inference. -/
local instance identityChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- The actual universal ambient ideal on the prescribed-basis chart. -/
def chartIdentityIdeal : Ideal (MvPolynomial I (ChartRing R I d w)) :=
  pointIdeal R I d w (S := ChartRing R I d w) (AlgHom.id R (ChartRing R I d w))

/-- The universal quotient has its actual prescribed polynomial basis. -/
def chartIdentityBasis : Module.Basis (Fin d) (ChartRing R I d w)
    (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  quotientBasis R I d w (ChartRing R I d w)
    (idealOfPoint R I d w (S := ChartRing R I d w) (AlgHom.id R (ChartRing R I d w)))

instance : Module.Free (ChartRing R I d w)
    (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  Module.Free.of_basis (chartIdentityBasis R I d w)

instance : Module.Finite (ChartRing R I d w)
    (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  Module.Finite.of_basis (chartIdentityBasis R I d w)

instance : Module.FinitePresentation (ChartRing R I d w)
    (MvPolynomial I (ChartRing R I d w) ⧸ chartIdentityIdeal R I d w) :=
  Module.finitePresentation_of_projective _ _

/-- Extending the universal ideal along a parameter gives its actual ambient ideal. -/
theorem chartIdentityIdeal_map {S : Type*} [CommRing S] [Algebra R S]
    (f : ChartRing R I d w →ₐ[R] S) :
    (chartIdentityIdeal R I d w).map (MvPolynomial.map f.toRingHom) = pointIdeal R I d w f := by
  let _ := pointScalars R I d w f
  let _ := pointTower R I d w f
  have h := chartClassification_natural R I d w (ChartRing R I d w) S
    (AlgHom.id R (ChartRing R I d w))
  exact (congrArg Subtype.val h).symm

end FLT.Mazur.HilbertChart
