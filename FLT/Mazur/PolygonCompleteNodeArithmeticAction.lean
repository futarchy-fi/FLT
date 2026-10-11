/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalCompletionModel
public import FLT.Mazur.PolygonCompleteNodeLocalFiniteness

/-!
# The actual complete local ring acts faithfully on its arithmetic model

The arithmetic completed xy=q ring receives the actual local ring through
its canonical completion and the constructed original-base comparison.
This action retains the original power-series coefficients and is faithfully flat.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual complete node local ring maps to the original arithmetic completed chart. -/
def completeNodeArithmeticScalars :
    (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i) →+*
      AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K)) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModel.scalars (completeNodeStalkCompletionAlgEquiv K n h i U hx)

/-- This local action retains each original power-series scalar. -/
theorem completeNodeArithmeticScalars_base (s : PowerSeries K) :
    completeNodeArithmeticScalars K n h i U hx (completeNodeStalkScalars K n h i U hx s) =
      algebraMap (PowerSeries K)
        (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
          (ChartRing (PowerSeries.X : PowerSeries K))) s := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModel.scalars_algebraMap
    (completeNodeStalkCompletionAlgEquiv K n h i U hx) s

/-- The formal arithmetic model is faithfully flat for its actual local-ring action. -/
theorem completeNodeArithmetic_faithfullyFlat :
    let _ : Algebra
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) :=
      (completeNodeArithmeticScalars K n h i U hx).toAlgebra
    let _ : Module
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
    Module.FaithfullyFlat
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModel.faithfullyFlat (completeNodeStalkCompletionAlgEquiv K n h i U hx)

/-- The original power-series and actual local-ring actions on the formal model agree. -/
theorem completeNodeArithmetic_scalarTower :
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    let _ : Algebra
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) :=
      (completeNodeArithmeticScalars K n h i U hx).toAlgebra
    let _ : Module
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) := Algebra.toModule
    let _ : SMul
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) :=
      ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
    IsScalarTower (PowerSeries K)
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i))
      (AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
        (ChartRing (PowerSeries.X : PowerSeries K))) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  exact LocalCompletionModel.scalarTower (completeNodeStalkCompletionAlgEquiv K n h i U hx)

end FLT.Mazur.PolygonInfinitesimalStages
