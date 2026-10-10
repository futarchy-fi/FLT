/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdentityIdeal
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Basic.Finite.Sum

/-!
# Noetherian integer Hilbert charts

With finitely many ambient generators, the structure-constant parameter ring
has finitely many variables. Over a Noetherian ring its basis chart and the
polynomial ambient are Noetherian, so the full universal ideal is finitely
presented. Integer charts therefore supply finite-presentation models.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart
variable (R I : Type*) [CommRing R] [IsNoetherianRing R] [Finite I] (d : ℕ)

/-- There are finitely many multiplication, unit, and ambient coordinates. -/
instance finiteVariable : Finite (Variable I d) := by
  let f : (Fin d × Fin d × Fin d) ⊕ (Fin d ⊕ (I × Fin d)) → Variable I d
    | .inl (i, j, k) => .mul i j k
    | .inr (.inl k) => .unit k
    | .inr (.inr (i, k)) => .generator i k
  apply Finite.of_surjective f
  intro x
  cases x with
  | mul i j k => exact ⟨.inl (i, j, k), rfl⟩
  | unit k => exact ⟨.inr (.inl k), rfl⟩
  | generator i k => exact ⟨.inr (.inr (i, k)), rfl⟩

/-- Cache the coefficient ring for nested Noetherian inference. -/
local instance noetherianCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for nested Noetherian inference. -/
local instance noetherianChartRing (w : Fin d → MvPolynomial I R) :
    CommRing (ChartRing R I d w) := inferInstance

/-- A finite-generator prescribed-basis chart is Noetherian over a Noetherian base. -/
instance chartRing_isNoetherian (w : Fin d → MvPolynomial I R) :
    IsNoetherianRing (ChartRing R I d w) := by
  let _ : IsNoetherianRing (Parameters R I d) := inferInstance
  let _ : IsNoetherianRing (Coefficients R I d) :=
    isNoetherianRing_of_surjective (Parameters R I d) (Coefficients R I d)
      (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  exact isNoetherianRing_of_surjective (Coefficients R I d) (ChartRing R I d w)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- The full universal ideal of a Noetherian chart is finitely presented. -/
theorem chartIdentityIdeal_finitePresentation (w : Fin d → MvPolynomial I R) :
    Module.FinitePresentation (MvPolynomial I (ChartRing R I d w))
      (chartIdentityIdeal R I d w) :=
  Module.finitePresentation_of_finite
    (MvPolynomial I (ChartRing R I d w)) (chartIdentityIdeal R I d w)

end FLT.Mazur.HilbertChart
