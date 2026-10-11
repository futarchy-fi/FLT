/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionFiltrationTransport
public import FLT.Mazur.PolygonCompleteNodeArithmeticAction
public import FLT.Mazur.PolygonCompleteNodeStalkEvaluation

/-!
# The actual node comparison preserves original ideal filtrations

The maximal-ideal filtration from the original stalk and the coordinate-ideal
filtration from the original arithmetic chart agree on their common completion.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Every positive evaluation vanishes on the same elements under the actual comparison. -/
theorem completeNodeStalkCompletion_eval_zero_iff (m : ℕ)
    (a : AdicCompletion (IsLocalRing.maximalIdeal
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))) :
    AdicCompletion.evalₐ (coordinateIdeal (PowerSeries.X : PowerSeries K)) (m + 1)
        (completeNodeStalkCompletionAlgEquiv K n h i U hx a) = 0 ↔
      AdicCompletion.evalₐ (IsLocalRing.maximalIdeal
        ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
          (m + 1) a = 0 := by
  rw [completeNodeStalkCompletionAlgEquiv_eval]
  simp only [map_eq_zero_iff _ (completeNodeArithmeticNeighborhood K n h i U hx m).injective,
    map_eq_zero_iff _ (AffineClosedPointQuotient.equivalence U
      ⟨completeNode K n h i, hx⟩ (completeNode_isClosed K n h i) (m + 1)).symm.injective]

/-- All extended original ideal powers agree through the actual node completion comparison. -/
theorem completeNodeStalkCompletion_map_power (m : ℕ) :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let I := IsLocalRing.maximalIdeal A
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    ((I ^ m).map (algebraMap A (AdicCompletion I A))).map
        (completeNodeStalkCompletionAlgEquiv K n h i U hx).toRingHom =
      (J ^ m).map (algebraMap B (AdicCompletion J B)) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  apply AdicCompletionFiltrationTransport.map_power
    _ _ (Ideal.fg_of_isNoetherianRing _) (Ideal.fg_of_isNoetherianRing _)
  intro a
  cases m with
  | zero =>
    rw [← AdicCompletionFiltrationTransport.mem_map_power_iff _
      (Ideal.fg_of_isNoetherianRing _),
      ← AdicCompletionFiltrationTransport.mem_map_power_iff _
        (Ideal.fg_of_isNoetherianRing _)]
    rw [pow_zero, pow_zero, Ideal.one_eq_top, Ideal.one_eq_top,
      Ideal.map_top, Ideal.map_top]
    trivial
  | succ m => exact completeNodeStalkCompletion_eval_zero_iff K n h i U hx m a

/-- The original local action sends the maximal ideal to the original coordinate ideal. -/
theorem completeNodeArithmeticScalars_map_maximalIdeal :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    (IsLocalRing.maximalIdeal A).map (completeNodeArithmeticScalars K n h i U hx) =
      (coordinateIdeal (PowerSeries.X : PowerSeries K)).map
        (algebraMap (ChartRing (PowerSeries.X : PowerSeries K))
          (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
            (ChartRing (PowerSeries.X : PowerSeries K)))) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  have hp := completeNodeStalkCompletion_map_power K n h i U hx 1
  dsimp only at hp ⊢
  rw [pow_one] at hp
  have hJ := pow_one (coordinateIdeal (PowerSeries.X : PowerSeries K))
  rw [hJ] at hp
  simpa [Ideal.map_map, completeNodeArithmeticScalars,
    LocalCompletionModel.scalars] using hp

end FLT.Mazur.PolygonInfinitesimalStages
