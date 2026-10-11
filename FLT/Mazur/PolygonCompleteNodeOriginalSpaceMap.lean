/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedInfinitesimalSpaceMap
public import FLT.Mazur.PolygonCompleteNodeCompletedLift

/-!
# Original degree-zero maps for both actual node presentations

The formal node comparison supplies maps in both directions between the
completed ORIGINAL presentation cotangent spaces. These maps use the
constructed infinitesimal lifts, with the actual formal scalar equivalence.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual affine node has a degree-zero map to the original arithmetic presentation. -/
def completeNodeOriginalSpaceMap :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators
    let Q := (chartGenerators (PowerSeries.X : PowerSeries K)).toExtension
    AdicCompletion (completeNodeAffineIdeal K n h i U hx) P.toExtension.CotangentSpace
      →ₛₗ[(completeNodeCompletionAlgEquiv K n h i U hx).toRingHom]
        AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K)) Q.CotangentSpace := by
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
  exact AdicCompletedInfinitesimalSpaceMap.map P Q (completeNodeAffineIdeal K n h i U hx)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCompletionAlgEquiv K n h i U hx)

/-- The original arithmetic degree-zero space maps back to the actual affine presentation. -/
def completeNodeOriginalSpaceReverseMap :
    let _ := (completeAffineScalars K n h U).toAlgebra
    let _ := completeAffine_finitePresentation K n h U
    let P := chartGenerators (PowerSeries.X : PowerSeries K)
    let Q := (Algebra.Presentation.ofFinitePresentation
      (PowerSeries K) Γ(exactVeroneseProj K n h, U)).toGenerators.toExtension
    AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K)) P.toExtension.CotangentSpace
      →ₛₗ[(completeNodeCompletionAlgEquiv K n h i U hx).symm.toRingHom]
        AdicCompletion (completeNodeAffineIdeal K n h i U hx) Q.CotangentSpace := by
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
  exact AdicCompletedInfinitesimalSpaceMap.map P Q
    (coordinateIdeal (PowerSeries.X : PowerSeries K)) (completeNodeAffineIdeal K n h i U hx)
    (completeNodeCompletionAlgEquiv K n h i U hx).symm

end FLT.Mazur.PolygonInfinitesimalStages
