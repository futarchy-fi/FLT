/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentTransportEquiv
public import FLT.Mazur.PolygonCompleteNodeCotangentComparison

/-!
# The actual node's equivalence of completed original cotangent modules

The formal arithmetic comparison identifies completed original stalk
differentials with completed original arithmetic differentials.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] AdicCotangentTransportMap.map
attribute [local instance] AdicCotangentTransportMap.inversePair
  AdicCotangentTransportMap.inversePairSymm

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual node comparison is an equivalence on completed original cotangent modules. -/
def completeNodeCotangentEquiv :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let I := IsLocalRing.maximalIdeal A
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    LinearEquiv (completeNodeStalkCompletionAlgEquiv K n h i U hx).toRingHom
      (σ' := (completeNodeStalkCompletionAlgEquiv K n h i U hx).symm.toRingHom)
      (AdicCompletion I Ω[A⁄PowerSeries K]) (AdicCompletion J Ω[B⁄PowerSeries K]) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeDifferentials_finitePresentation K n h i U hx
  refine AdicCotangentTransportMap.equiv _ _
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) ?_
  have he := completeNodeStalkCompletion_map_power K n h i U hx 1
  dsimp only at he
  rw [pow_one, pow_one (coordinateIdeal (PowerSeries.X : PowerSeries K))] at he
  exact he

/-- The equivalence retains the original comparison map on every element. -/
@[simp] theorem completeNodeCotangentEquiv_apply :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    ∀ x : AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K],
      completeNodeCotangentEquiv K n h i U hx x =
        completeNodeCotangentComparison K n h i U hx x := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  dsimp only
  intro x
  rfl

/-- Inverting the comparison recovers each original differential from its formal derivative. -/
theorem completeNodeCotangentEquiv_symm_of_D :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    ∀ a : A, (completeNodeCotangentEquiv K n h i U hx).symm
      (AdicDerivationFiltration.completion
        (KaehlerDifferential.D (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))
        (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (completeNodeStalkCompletionAlgEquiv K n h i U hx
          (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a))) =
      AdicCompletion.of (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
        (KaehlerDifferential.D (PowerSeries K) A a) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  dsimp only
  intro a
  rw [← completeNodeCotangentComparison_of_D, ← completeNodeCotangentEquiv_apply]
  exact (completeNodeCotangentEquiv K n h i U hx).symm_apply_apply _

end FLT.Mazur.PolygonInfinitesimalStages
