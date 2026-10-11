/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModelFiniteEquiv
public import FLT.Mazur.PolygonCompleteNodeArithmeticAction
public import FLT.Mazur.PolygonCompleteNodeStalkH1Equiv

/-!
# Original stalk H1 in the faithfully flat arithmetic model

The constructed completed-stalk comparison is linear over the arithmetic
completion after extending the original stalk H1 through its actual action.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeStalkH1Equiv
attribute [local instance] TensorAlgebraSemilinearEquiv.forwardInverse
  TensorAlgebraSemilinearEquiv.reverseInverse

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Actual stalk H1, extended by its actual local action, is completed original arithmetic H1. -/
def completeNodeArithmeticH1Equiv :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let D := AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ : Algebra L D := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
    let _ : Module L D := Algebra.toModule
    (D ⊗[L] Algebra.H1Cotangent (PowerSeries K) L) ≃ₗ[D]
      AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (Algebra.H1Cotangent (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K))) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeH1Cotangent_finite K n h i U hx
  exact LocalCompletionModelFiniteEquiv.equiv
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) _
    (completeNodeStalkH1Equiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
