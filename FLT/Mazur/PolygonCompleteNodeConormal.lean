/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalConormal
public import FLT.Mazur.PolygonCompleteNodeInfinitesimalLift

/-!
# Original conormals of the two actual node presentations

Both the actual affine presentation and the arithmetic node presentation
retain their original conormals after infinitesimalization and completion.
The comparisons are linear over their respective actual completed targets.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing AdicFormalPresentationHom

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual affine node's completed infinitesimal conormal is its completed original conormal. -/
def completeNodeOriginalConormalEquiv :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
    let I := completeNodeAffineIdeal K n h i U hx
    AdicCompletion I P.Cotangent ≃ₗ[AdicCompletion I Γ(exactVeroneseProj K n h, U)]
      (completed P.infinitesimal I).Cotangent := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let P := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
  let _ : IsNoetherianRing P.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  exact AdicInfinitesimalConormal.equiv P (completeNodeAffineIdeal K n h i U hx)

/-- The arithmetic node comparison retains the conormal of the original xy=q presentation. -/
def arithmeticNodeOriginalConormalEquiv :
    let P := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    let I := coordinateIdeal (PowerSeries.X : PowerSeries K)
    AdicCompletion I P.Cotangent ≃ₗ[
      AdicCompletion I (ChartRing (PowerSeries.X : PowerSeries K))]
      (completed P.infinitesimal I).Cotangent := by
  let P := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
  let _ : IsNoetherianRing P.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  exact AdicInfinitesimalConormal.equiv P (coordinateIdeal (PowerSeries.X : PowerSeries K))

end FLT.Mazur.PolygonInfinitesimalStages
