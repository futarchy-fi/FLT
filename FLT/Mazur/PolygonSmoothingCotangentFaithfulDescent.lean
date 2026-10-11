/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FaithfulTensorVanishing
public import FLT.Mazur.PolygonSmoothingLocalizedCotangent
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Faithful descent of arithmetic cotangent flatness after inverting the original parameter

The arithmetic completed chart, acting faithfully flatly on an original
ring, detects flatness after localization at the ORIGINAL base parameter.
The localization and the faithful extension are assembled by tensor base change.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

open TensorProduct

universe u

variable {R : Type u} [CommRing R] (t : R)
  [IsNoetherianRing (ChartRing t)] (I : Ideal (ChartRing t))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A M : Type u} [CommRing A] [Algebra R A] [Algebra A (AdicCompletion I (ChartRing t))]
  [IsScalarTower R A (AdicCompletion I (ChartRing t))]
  [Module.FaithfullyFlat A (AdicCompletion I (ChartRing t))] [AddCommGroup M] [Module A M]
  (e : (AdicCompletion I (ChartRing t) ⊗[A] M) ≃ₗ[AdicCompletion I (ChartRing t)]
    AdicCompletion I (Ω[ChartRing t⁄R]))
  (B : Type u) [CommRing B] [Algebra A B]
  [IsLocalization.Away (algebraMap R A t) B]

include e in
/-- Arithmetic flatness descends to localization of the original module at the original t. -/
theorem cotangentModel_away_flat : Module.Flat B (B ⊗[A] M) := by
  let D := AdicCompletion I (ChartRing t)
  let S := B ⊗[A] D
  let _ : IsLocalization.Away (algebraMap A D (algebraMap R A t)) S := inferInstance
  have ht : IsUnit (algebraMap D S (algebraMap R D t)) := by
    rw [IsScalarTower.algebraMap_apply R A D]
    exact IsLocalization.Away.algebraMap_isUnit (algebraMap A D (algebraMap R A t))
  let _ := Module.Flat.of_linearEquiv (completedCotangentUnitEquiv t I S ht)
  exact FaithfulTensorVanishing.flat (S := S) e

end FLT.Mazur.PolygonSmoothing
