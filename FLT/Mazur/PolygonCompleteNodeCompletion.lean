/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionPositiveEquiv
public import FLT.Mazur.PolygonNodeNeighborhoodTransition

/-!
# The actual complete node neighborhood completion over its original base

The previously constructed comparisons retain the original power-series
coefficients and adjacent restrictions. Their limit identifies completion
at the specified complete affine node with the arithmetic xy=q completion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Each existing arithmetic neighborhood comparison is over the original complete base. -/
def completeNodeArithmeticNeighborhoodAlgEquiv (m : ℕ) :
    let _ := (completeAffineScalars K n h U).toAlgebra
    (Γ(exactVeroneseProj K n h, U) ⧸
      completeNodeAffineIdeal K n h i U hx ^ (m + 1)) ≃ₐ[PowerSeries K]
        (ChartRing (PowerSeries.X : PowerSeries K) ⧸
        coordinateIdeal (PowerSeries.X : PowerSeries K) ^ (m + 1)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  refine { completeNodeArithmeticNeighborhood K n h i U hx m with commutes' := ?_ }
  intro r
  exact completeNodeArithmeticNeighborhood_scalar K n h i U hx m r

/-- Completion at the actual complete affine node is its original arithmetic xy=q completion. -/
def completeNodeCompletionAlgEquiv :
    let _ := (completeAffineScalars K n h U).toAlgebra
    AdicCompletion (completeNodeAffineIdeal K n h i U hx)
      Γ(exactVeroneseProj K n h, U) ≃ₐ[PowerSeries K]
        AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
          (ChartRing (PowerSeries.X : PowerSeries K)) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  exact AdicCompletionPositiveEquiv.equivalence
    (completeNodeAffineIdeal K n h i U hx)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeArithmeticNeighborhoodAlgEquiv K n h i U hx)
    (completeNodeArithmeticNeighborhood_transition K n h i U hx)

/-- Every finite evaluation is precisely the original actual neighborhood comparison. -/
theorem completeNodeCompletionAlgEquiv_eval (m : ℕ)
    (a : AdicCompletion (completeNodeAffineIdeal K n h i U hx)
      Γ(exactVeroneseProj K n h, U)) :
    AdicCompletion.evalₐ (coordinateIdeal (PowerSeries.X : PowerSeries K)) (m + 1)
      (completeNodeCompletionAlgEquiv K n h i U hx a) =
        completeNodeArithmeticNeighborhood K n h i U hx m
          (AdicCompletion.evalₐ (completeNodeAffineIdeal K n h i U hx) (m + 1) a) := by
  let _ := (completeAffineScalars K n h U).toAlgebra
  exact AdicCompletionPositiveEquiv.eval_equivalence
    (completeNodeAffineIdeal K n h i U hx)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeArithmeticNeighborhoodAlgEquiv K n h i U hx)
    (completeNodeArithmeticNeighborhood_transition K n h i U hx) m a

end FLT.Mazur.PolygonInfinitesimalStages
