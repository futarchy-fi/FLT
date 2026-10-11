/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeArithmeticH1Equiv
public import FLT.Mazur.PolygonSmoothingH1FaithfulDescent

/-!
# Vanishing of original node H1 after inverting the original parameter

The actual node stalk acts faithfully flatly on its arithmetic completed
model. Original H1 vanishing descends from that model after localization
at the original power-series parameter.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeArithmeticH1Equiv

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- Inverting the original q kills scalar extension of the original actual node-stalk H1. -/
theorem completeNodeH1_away (B : Type) [CommRing B]
    [Algebra ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) B]
    [IsLocalization.Away (completeNodeStalkScalars K n h i U hx PowerSeries.X) B] :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Subsingleton (B ⊗[L] Algebra.H1Cotangent (PowerSeries K) L) := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
  let D := AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (ChartRing (PowerSeries.X : PowerSeries K))
  let _ : Algebra L D := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
  let _ : Module L D := Algebra.toModule
  let _ : SMul L D := ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
  let _ : IsScalarTower (PowerSeries K) L D := completeNodeArithmetic_scalarTower K n h i U hx
  let _ : Module.FaithfullyFlat L D := completeNodeArithmetic_faithfullyFlat K n h i U hx
  exact h1Model_away_subsingleton (PowerSeries.X : PowerSeries K)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeArithmeticH1Equiv K n h i U hx) B

/-- Actual first cotangent homology vanishes on the original node stalk with q inverted. -/
theorem completeNodeGenericH1_subsingleton :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let q := completeNodeStalkScalars K n h i U hx PowerSeries.X
    let B := Localization.Away q
    let _ := ((algebraMap L B).comp (completeNodeStalkScalars K n h i U hx)).toAlgebra
    Subsingleton (Algebra.H1Cotangent (PowerSeries K) B) := by
  let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
  let q := completeNodeStalkScalars K n h i U hx PowerSeries.X
  let B := Localization.Away q
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let _ := ((algebraMap L B).comp (completeNodeStalkScalars K n h i U hx)).toAlgebra
  let _ : Module L B := Algebra.toModule
  let _ : Module (PowerSeries K) B := Algebra.toModule
  let _ : SMul L B := Algebra.toSMul
  let _ : SMul (PowerSeries K) B := Algebra.toSMul
  let _ : IsScalarTower (PowerSeries K) L B := IsScalarTower.of_algebraMap_eq' rfl
  let _ := completeNodeH1_away K n h i U hx B
  exact (Algebra.tensorH1CotangentOfIsLocalization (PowerSeries K) B
    (Submonoid.powers q)).symm.subsingleton

end FLT.Mazur.PolygonInfinitesimalStages
