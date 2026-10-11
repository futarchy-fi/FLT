/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletedDifferentials
public import FLT.Mazur.LocalCompletionModelModule
public import FLT.Mazur.PolygonCompleteNodeModuleFiltration

/-!
# The arithmetic model acts on the actual completed original cotangent module

The inverse of the actual local comparison transports the completed stalk's
original differentials. The original stalk and power-series actions survive.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The arithmetic completion acts on the completion of the original stalk differentials. -/
@[instance_reducible] def completeNodeCotangentArithmeticModule :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Module (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
      (ChartRing (PowerSeries.X : PowerSeries K)))
      (AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModelModule.modelModule
    (completeNodeStalkCompletionAlgEquiv K n h i U hx)

/-- The transported cotangent action retains every actual completed local scalar. -/
theorem completeNodeCotangentArithmetic_smul :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    ∀ (a : AdicCompletion (IsLocalRing.maximalIdeal A) A)
      (x : AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]),
      completeNodeStalkCompletionAlgEquiv K n h i U hx a • x = a • x := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModelModule.modelModule_smul
    (completeNodeStalkCompletionAlgEquiv K n h i U hx)

/-- The original power-series action is retained on the transported original cotangent module. -/
theorem completeNodeCotangentArithmetic_baseScalarTower :
    let A := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ := completeNodeCotangentArithmeticModule K n h i U hx
    IsScalarTower (PowerSeries K)
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K)))
      (AdicCompletion (IsLocalRing.maximalIdeal A) Ω[A⁄PowerSeries K]) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModelModule.relativeScalarTower
    (completeNodeStalkCompletionAlgEquiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
