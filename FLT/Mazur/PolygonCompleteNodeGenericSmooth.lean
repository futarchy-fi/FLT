/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LocalizedOriginalSmoothCriterion
public import FLT.Mazur.PolygonCompleteNodeGenericDifferentials
public import FLT.Mazur.PolygonCompleteNodeGenericH1

/-!
# Formal smoothness of the actual node stalk after inverting original q

Both original cotangent obstructions descend from the arithmetic model.
They give formal smoothness of the ORIGINAL node stalk localized at q.
This is a local statement, not yet a full-chart or generic-fiber assertion.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.PolygonInfinitesimalStages

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual original node stalk becomes formally smooth after inverting its original q. -/
theorem completeNodeGeneric_formallySmooth :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let q := completeNodeStalkScalars K n h i U hx PowerSeries.X
    let B := Localization.Away q
    let _ := ((algebraMap L B).comp (completeNodeStalkScalars K n h i U hx)).toAlgebra
    Algebra.FormallySmooth (PowerSeries K) B := by
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
  let _ : Algebra.EssFiniteType (PowerSeries K) L :=
    completeNodeStalkScalars_essFiniteType K n h i U hx
  let _ : Algebra.EssFiniteType (PowerSeries K) B := Algebra.EssFiniteType.comp _ L _
  let _ := completeNodeH1_away K n h i U hx B
  let _ := completeNodeDifferentials_away_flat K n h i U hx B
  exact LocalizedOriginalSmoothCriterion.formallySmooth (PowerSeries K) L B (Submonoid.powers q)

end FLT.Mazur.PolygonInfinitesimalStages
