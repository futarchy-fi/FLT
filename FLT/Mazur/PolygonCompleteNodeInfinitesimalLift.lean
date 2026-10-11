/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicInfinitesimalPresentationLift
public import FLT.Mazur.PolygonCompleteAffinePresentation
public import FLT.Mazur.PolygonCompleteNodeCompletion
public import FLT.Mazur.PolygonSmoothingConormalMap

/-!
# Lifting the actual node comparison to infinitesimal presentations

The actual affine formal comparison lifts from the original finite polynomial
presentation to the completed arithmetic infinitesimal presentation. The lift
retains the given comparison on every original affine section.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing AdicExtensionProjection AdicInfinitesimalPresentationLift

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual finite affine infinitesimal presentation lifts to the arithmetic one. -/
def completeNodeInfinitesimalLift :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    let Q := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    P.toExtension.infinitesimal.Ring →ₐ[PowerSeries K]
      AdicCompletion (ideal Q.infinitesimal (coordinateIdeal (PowerSeries.X : PowerSeries K)))
        Q.infinitesimal.Ring := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  exact infinitesimalLift
    (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    (completeNodeAffineIdeal K n h i U hx) (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCompletionAlgEquiv K n h i U hx).toAlgHom

/-- The constructed infinitesimal lift lies over the actual original node comparison. -/
theorem completeNodeInfinitesimalLift_projection :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    let Q := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    ∀ x : P.toExtension.infinitesimal.Ring,
      projection Q.infinitesimal (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (completeNodeInfinitesimalLift K n h i U hx x) =
      completeNodeCompletionAlgEquiv K n h i U hx
        (algebraMap Γ(exactVeroneseProj K n h, U)
          (AdicCompletion (completeNodeAffineIdeal K n h i U hx)
            Γ(exactVeroneseProj K n h, U))
          (algebraMap P.toExtension.infinitesimal.Ring Γ(exactVeroneseProj K n h, U) x)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let _ : IsNoetherianRing (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension.Ring :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin 2) (PowerSeries K)))
  exact projection_infinitesimalLift
    (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    (completeNodeAffineIdeal K n h i U hx) (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCompletionAlgEquiv K n h i U hx).toAlgHom

/-- The inverse actual comparison lifts the arithmetic infinitesimal presentation as well. -/
def completeNodeInfinitesimalReverseLift :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    let Q := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
    P.infinitesimal.Ring →ₐ[PowerSeries K]
      AdicCompletion (ideal Q.infinitesimal (completeNodeAffineIdeal K n h i U hx))
        Q.infinitesimal.Ring := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let Q := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
  let _ : IsNoetherianRing Q.toExtension.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  exact infinitesimalLift (chartGenerators (PowerSeries.X : PowerSeries K)) Q.toExtension
    (coordinateIdeal (PowerSeries.X : PowerSeries K)) (completeNodeAffineIdeal K n h i U hx)
    (completeNodeCompletionAlgEquiv K n h i U hx).symm.toAlgHom

/-- The reverse lift retains the inverse actual formal comparison on original arithmetic classes. -/
theorem completeNodeInfinitesimalReverseLift_projection :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    let Q := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
    ∀ x : P.infinitesimal.Ring,
      projection Q.infinitesimal (completeNodeAffineIdeal K n h i U hx)
        (completeNodeInfinitesimalReverseLift K n h i U hx x) =
      (completeNodeCompletionAlgEquiv K n h i U hx).symm
        (algebraMap (ChartRing (PowerSeries.X : PowerSeries K))
          (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
            (ChartRing (PowerSeries.X : PowerSeries K)))
          (algebraMap P.infinitesimal.Ring (ChartRing (PowerSeries.X : PowerSeries K)) x)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  let _ := completeAffine_finitePresentation K n h U
  let Q := (Algebra.Presentation.ofFinitePresentation
    (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
  let _ : IsNoetherianRing Q.toExtension.Ring := inferInstanceAs
    (IsNoetherianRing (MvPolynomial (Fin (Algebra.Presentation.ofFinitePresentationVars
      (PowerSeries K) Γ(exactVeroneseProj K n h, U))) (PowerSeries K)))
  exact projection_infinitesimalLift
    (chartGenerators (PowerSeries.X : PowerSeries K)) Q.toExtension
    (coordinateIdeal (PowerSeries.X : PowerSeries K)) (completeNodeAffineIdeal K n h i U hx)
    (completeNodeCompletionAlgEquiv K n h i U hx).symm.toAlgHom

end FLT.Mazur.PolygonInfinitesimalStages
