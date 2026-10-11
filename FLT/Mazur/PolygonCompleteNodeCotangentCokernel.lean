/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeCotangentEquiv
public import FLT.Mazur.PolygonSmoothingCotangentCokernel

/-!
# An explicit cokernel for the actual node cotangent module

The actual stalk comparison identifies completed original differentials
with the one-relation quotient over the arithmetic completed ring.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] AdicCotangentTransportMap.map
  completedCotangentCokernelEquiv completeNodeCotangentEquiv
attribute [local instance] AdicCotangentTransportMap.inversePair
  AdicCotangentTransportMap.inversePairSymm

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual completed original cotangent module has the explicit arithmetic cokernel. -/
def completeNodeCotangentCokernelEquiv :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    LinearEquiv (completeNodeStalkCompletionAlgEquiv K n h i U hx).toRingHom
      (σ' := (completeNodeStalkCompletionAlgEquiv K n h i U hx).symm.toRingHom)
      (AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K])
      (CompletedCotangentCokernel (PowerSeries.X : PowerSeries K)
        (coordinateIdeal (PowerSeries.X : PowerSeries K))) :=
  (completeNodeCotangentEquiv K n h i U hx).trans
    (completedCotangentCokernelEquiv (PowerSeries.X : PowerSeries K)
      (coordinateIdeal (PowerSeries.X : PowerSeries K)))

/-- The explicit presentation sends every original differential through its actual formal image. -/
theorem completeNodeCotangentCokernelEquiv_of_D :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    ∀ a : A, completeNodeCotangentCokernelEquiv K n h i U hx
      (AdicCompletion.of (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
        (KaehlerDifferential.D (PowerSeries K) A a)) =
      completedCotangentCokernelEquiv (PowerSeries.X : PowerSeries K)
        (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (AdicDerivationFiltration.completion
          (KaehlerDifferential.D (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))
          (coordinateIdeal (PowerSeries.X : PowerSeries K))
          (completeNodeStalkCompletionAlgEquiv K n h i U hx
            (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a))) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  dsimp only
  intro a
  change completedCotangentCokernelEquiv (PowerSeries.X : PowerSeries K)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeCotangentEquiv K n h i U hx _) = _
  rw [completeNodeCotangentEquiv_apply, completeNodeCotangentComparison_of_D]

end FLT.Mazur.PolygonInfinitesimalStages
