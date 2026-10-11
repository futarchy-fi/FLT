/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingCotangentFaithfulDescent
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Rank one of the original cotangent module at punctured field points

The arithmetic completed model is used only as a faithfully flat test.
Tensoring both models to a common overring and comparing ranks computes
the original field-valued cotangent space, without replacing it by a completion.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PolygonSmoothing

open TensorProduct

universe u

variable {R : Type u} [CommRing R] (t : R)
  [IsNoetherianRing (ChartRing t)] (I : Ideal (ChartRing t))

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A M : Type u} [CommRing A] [Algebra R A]
  [Algebra A (AdicCompletion I (ChartRing t))]
  [IsScalarTower R A (AdicCompletion I (ChartRing t))]
  [Module.FaithfullyFlat A (AdicCompletion I (ChartRing t))]
  [AddCommGroup M] [Module A M]
  (e : (AdicCompletion I (ChartRing t) ⊗[A] M) ≃ₗ[AdicCompletion I (ChartRing t)]
    AdicCompletion I (Ω[ChartRing t⁄R]))
  (B : Type u) [Field B] [Algebra A B]

include e in
/-- Every original field-valued cotangent space away from t has dimension one. -/
theorem cotangentModel_field_finrank
    (ht : IsUnit (algebraMap A B (algebraMap R A t))) :
    Module.finrank B (B ⊗[A] M) = 1 := by
  let D := AdicCompletion I (ChartRing t)
  let S := B ⊗[A] D
  have hts : IsUnit (algebraMap D S (algebraMap R D t)) := by
    rw [IsScalarTower.algebraMap_apply R A D,
      ← IsScalarTower.algebraMap_apply A D S, IsScalarTower.algebraMap_apply A B S]
    exact ht.map (algebraMap B S)
  let f : (S ⊗[B] (B ⊗[A] M)) ≃ₗ[S] S :=
    (FaithfulTensorVanishing.equiv (B := B) (S := S) e).trans
      (completedCotangentUnitEquiv t I S hts)
  have he := f.finrank_eq
  simpa only [Module.finrank_baseChange, Module.finrank_self] using he

end FLT.Mazur.PolygonSmoothing
