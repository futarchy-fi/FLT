/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteNodeArithmeticDifferentials
public import FLT.Mazur.PolygonSmoothingCotangentFieldRank

/-!
# Rank of actual node differentials at punctured field points

The faithfully flat arithmetic model computes the rank of the ORIGINAL
node differential module after any field-valued change of its stalk scalars
that makes the ORIGINAL power-series parameter nonzero.
-/

@[expose] public noncomputable section

open AlgebraicGeometry
open scoped TensorProduct

namespace FLT.Mazur.PolygonInfinitesimalStages

open PolygonSmoothing

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] exactVeroneseProj originalStageToCompatibleProj
attribute [local irreducible] completeNodeArithmeticDifferentialsEquiv

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
  (U : (exactVeroneseProj K n h).affineOpens) (hx : completeNode K n h i ∈ U.1)

/-- The actual node cotangent space has dimension one at every punctured field point. -/
theorem completeNodeDifferentials_field_finrank (B : Type) [Field B]
    [Algebra ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) B]
    (ht : IsUnit (algebraMap
      ((exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)) B
        (completeNodeStalkScalars K n h i U hx PowerSeries.X))) :
    let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
    let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
    Module.finrank B (B ⊗[L] Ω[L⁄PowerSeries K]) = 1 := by
  let _ := (completeNodeStalkScalars K n h i U hx).toAlgebra
  let L := (exactVeroneseProj K n h).presheaf.stalk (completeNode K n h i)
  let D := AdicCompletion (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (ChartRing (PowerSeries.X : PowerSeries K))
  let _ : Algebra L D := (completeNodeArithmeticScalars K n h i U hx).toAlgebra
  let _ : Module L D := Algebra.toModule
  let _ : SMul L D := ⟨fun a c ↦ completeNodeArithmeticScalars K n h i U hx a * c⟩
  let _ : IsScalarTower (PowerSeries K) L D := completeNodeArithmetic_scalarTower K n h i U hx
  let _ : Module.FaithfullyFlat L D := completeNodeArithmetic_faithfullyFlat K n h i U hx
  exact cotangentModel_field_finrank (PowerSeries.X : PowerSeries K)
    (coordinateIdeal (PowerSeries.X : PowerSeries K))
    (completeNodeArithmeticDifferentialsEquiv K n h i U hx) B ht

end FLT.Mazur.PolygonInfinitesimalStages
