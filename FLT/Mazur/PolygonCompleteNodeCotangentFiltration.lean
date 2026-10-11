/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModelFiltration
public import FLT.Mazur.PolygonCompleteNodeCotangentAction

/-!
# The actual original cotangent filtration on the arithmetic node model

The completed original stalk differentials retain their entire original
filtration. Under the transported action they are arithmetic-adically separated.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual completed cotangent filtration is exactly the original arithmetic filtration. -/
theorem completeNodeCotangentArithmetic_mem_power_iff :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let M := AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    let _ := Module.compHom M (algebraMap B (AdicCompletion J B))
    ∀ (m : ℕ) (x : M),
      x ∈ IsLocalRing.maximalIdeal A ^ m • (⊤ : Submodule A M) ↔
        x ∈ J ^ m • (⊤ : Submodule B M) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModelFiltration.mem_power_iff
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) _
    (completeNodeArithmeticScalars_map_maximalIdeal K n h i U hx)

/-- The transported actual cotangent module is separated for the original arithmetic ideal. -/
theorem completeNodeCotangentArithmetic_isHausdorff :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let M := AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]
    let B := ChartRing (PowerSeries.X : PowerSeries K)
    let J := coordinateIdeal (PowerSeries.X : PowerSeries K)
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    let _ := Module.compHom M (algebraMap B (AdicCompletion J B))
    IsHausdorff J M := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModelFiltration.isHausdorff
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) _
    (completeNodeArithmeticScalars_map_maximalIdeal K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
