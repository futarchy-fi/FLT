/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModelFiniteEquiv
public import FLT.Mazur.PolygonCompleteNodeArithmeticAction
public import FLT.Mazur.PolygonCompleteNodeCotangentEquiv

/-!
# Original stalk differentials in the faithfully flat arithmetic model

The constructed completed-stalk comparison is linear over the arithmetic
completion after extending the original stalk differentials through its actual action.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeCotangentEquiv
attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Actual stalk differentials extend to completed original arithmetic differentials. -/
def completeNodeArithmeticDifferentialsEquiv :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let D := AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ : Algebra L D := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
    let _ : Module L D := Algebra.toModule
    (D ⊗[L] Ω[L⁄PowerSeries K]) ≃ₗ[D]
      AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (Ω[ChartRing (PowerSeries.X : PowerSeries K)⁄PowerSeries K]) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeDifferentials_finitePresentation K n h i U hx
  exact LocalCompletionModelFiniteEquiv.equiv
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) _
    (completeNodeCotangentEquiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
