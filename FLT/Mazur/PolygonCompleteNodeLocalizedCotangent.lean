/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeCotangentEquiv
public import FLT.Mazur.PolygonSmoothingLocalizedCotangent

/-!
# The actual completed node cotangent module over the punctured base

The arithmetic action on completed original stalk differentials turns the
formal comparison into a linear equivalence. After inverting the original
power-series parameter, its scalar extension is a free rank-one module.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeCotangentEquiv completedCotangentLocalizedEquiv
attribute [local instance] AdicCotangentTransportMap.inversePair
  AdicCotangentTransportMap.inversePairSymm

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- With its constructed arithmetic action, the actual cotangent comparison is linear. -/
def completeNodeCotangentArithmeticEquiv :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K] ≃ₗ[AdicCompletion J B]
      AdicCompletion J Ω[B⁄PowerSeries K] := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeCotangentArithmeticModule K n h i U hx
  let e := completeNodeStalkCompletionAlgEquiv K n h i U hx
  let f := completeNodeCotangentEquiv K n h i U hx
  refine { f.toAddEquiv with map_smul' := ?_ }
  intro b x
  change f (e.symm b • x) = b • f x
  calc
    f (e.symm b • x) = e (e.symm b) • f x := f.map_smulₛₗ _ _
    _ = b • f x := by rw [e.apply_symm_apply]

/-- Inverting the original parameter makes actual completed original cotangents rank one. -/
def completeNodeLocalizedCotangentEquiv (S : Type*) [CommRing S]
    [Algebra (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))) S]
    [IsLocalization.Away
      (algebraMap (PowerSeries K)
        (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
          (ChartRing (PowerSeries.X : PowerSeries K))) PowerSeries.X) S] :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    S ⊗[AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K))]
      AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K] ≃ₗ[S] S := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeCotangentArithmeticModule K n h i U hx
  exact ((completeNodeCotangentArithmeticEquiv K n h i U hx).baseChange _ S _ _).trans
    (completedCotangentLocalizedEquiv (PowerSeries.X : PowerSeries K)
      (coordinateIdeal (PowerSeries.X : PowerSeries K)) S)

end FLT.Mazur.PolygonInfinitesimalStages
