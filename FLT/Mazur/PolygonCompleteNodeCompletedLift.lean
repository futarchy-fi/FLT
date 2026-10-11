/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedInfinitesimalLift
public import FLT.Mazur.PolygonCompleteNodeInfinitesimalLift
public import FLT.Mazur.PolygonArithmeticNodePoint

/-!
# Completed infinitesimal lifts for the actual arithmetic node

The constructed forward and reverse infinitesimal lifts extend through their
actual presenting-ring completions. Their continuity is proved from maximal
ideals and the actual formal node equivalence, with no lifting assumptions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing AdicExtensionProjection

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The forward actual node lift extends through both infinitesimal presentation completions. -/
def completeNodeCompletedInfinitesimalLift :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    let Q := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    AdicCompletion (ideal P.toExtension.infinitesimal (completeNodeAffineIdeal K n h i U hx))
      P.toExtension.infinitesimal.Ring →ₐ[PowerSeries K]
        AdicCompletion (ideal Q.infinitesimal (coordinateIdeal (PowerSeries.X : PowerSeries K)))
          Q.infinitesimal.Ring := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let P := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
  let Q := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
  let _ : IsNoetherianRing P.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  let _ : IsNoetherianRing Q.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  let _ := arithmeticNodeIdeal_isMaximal K
  exact AdicCompletedInfinitesimalLift.lift P Q (completeNodeAffineIdeal K n h i U hx)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCompletionAlgEquiv K n h i U hx)

/-- The reverse arithmetic lift also extends through the actual presentation completions. -/
def completeNodeCompletedInfinitesimalReverseLift :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := chartGenerators (PowerSeries.X : PowerSeries K)
    let Q := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
    AdicCompletion (ideal P.toExtension.infinitesimal
      (coordinateIdeal (PowerSeries.X : PowerSeries K))) P.toExtension.infinitesimal.Ring
        →ₐ[PowerSeries K]
      AdicCompletion (ideal Q.infinitesimal (completeNodeAffineIdeal K n h i U hx))
        Q.infinitesimal.Ring := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let P := chartGenerators (PowerSeries.X : PowerSeries K)
  let Q := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
  let _ : IsNoetherianRing P.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  let _ : IsNoetherianRing Q.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  let _ := arithmeticNodeIdeal_isMaximal K
  exact AdicCompletedInfinitesimalLift.lift P Q
    (coordinateIdeal (PowerSeries.X : PowerSeries K)) (completeNodeAffineIdeal K n h i U hx)
    (completeNodeCompletionAlgEquiv K n h i U hx).symm

end FLT.Mazur.PolygonInfinitesimalStages
