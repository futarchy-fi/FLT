/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCotangentTransportMap
public import FLT.Mazur.PolygonCompleteNodeCotangentFiltration

/-!
# The actual node's map of completed original cotangent modules

The constructed formal comparison differentiates to a semilinear map from
actual stalk differentials to arithmetic differentials, preserving original germs.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] AdicCotangentTransportMap.map

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Differentiate the actual local comparison on the completed original cotangent modules. -/
def completeNodeCotangentComparison :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let I := IsLocalRing.maximalIdeal A
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    AdicCompletion I Ω[A⁄PowerSeries K] →ₛₗ[
      (completeNodeStalkCompletionAlgEquiv K n h i U hx).toRingHom]
        AdicCompletion J Ω[B⁄PowerSeries K] := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeDifferentials_finitePresentation K n h i U hx
  exact AdicCotangentTransportMap.map _ _ (completeNodeStalkCompletionAlgEquiv K n h i U hx)

/-- Each original stalk differential maps to the derivative of its actual formal image. -/
theorem completeNodeCotangentComparison_of_D :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    ∀ a : A, completeNodeCotangentComparison K n h i U hx
      (AdicCompletion.of (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
        (KaehlerDifferential.D (PowerSeries K) A a)) =
      AdicDerivationFiltration.completion
        (KaehlerDifferential.D (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))
        (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (completeNodeStalkCompletionAlgEquiv K n h i U hx
          (AdicCompletion.of (IsLocalRing.maximalIdeal A) A a)) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := completeNodeDifferentials_finitePresentation K n h i U hx
  dsimp only
  intro a
  unfold completeNodeCotangentComparison
  exact AdicCotangentTransportMap.map_of_D (R := PowerSeries K)
    (IsLocalRing.maximalIdeal
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)))
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) a

/-- The cotangent comparison retains the original affine germs in the actual arithmetic model. -/
theorem completeNodeCotangentComparison_of_germ :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    ∀ a : Γ(exactVeroneseProj K n h, U), completeNodeCotangentComparison K n h i U hx
      (AdicCompletion.of (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
        (KaehlerDifferential.D (PowerSeries K) A
          ((exactVeroneseProj K n h).presheaf.germ U (completeNode K n h i) hx a))) =
      AdicDerivationFiltration.completion
        (KaehlerDifferential.D (PowerSeries K) (ChartRing (PowerSeries.X : PowerSeries K)))
        (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (completeNodeCompletionAlgEquiv K n h i U hx
          (AdicCompletion.of (completeNodeAffineIdeal K n h i U hx) _ a)) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  dsimp only
  intro a
  rw [completeNodeCotangentComparison_of_D, ← completeNodeGermCompletion_of,
    completeNodeStalkCompletionAlgEquiv_germ]

end FLT.Mazur.PolygonInfinitesimalStages
