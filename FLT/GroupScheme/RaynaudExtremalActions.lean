/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudMinimalModel
public import FLT.GroupScheme.RaynaudScalarAction

/-!
# Actual scalar actions on maximal and minimal models

Both extremal models are constructed independently of small ramification.
Their integral scalar maps extend the prescribed generic action and satisfy
zero, unit, addition and composition laws.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan

variable {R K F : Type} [CommRing R] [Field K] [Algebra R K]
  [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R K] [CharZero K] [Semiring F]
  (X : FF R K) [Module F X.Points]
  [SMulCommClass F (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) X.Points]

/-- Construct the maximum with the actual prescribed scalar action and its laws. -/
theorem exists_maximal_model_scalar_action :
    ∃ (M : FF R K) (f : GenericGaloisHom X M) (lift : F → ModelHom M M),
      Function.Bijective f ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom M Y), ∃! h : ModelHom M Y, genericHom h = g) ∧
      (∀ a x, genericHom (lift a) (f x) = f (a • x)) ∧
      lift 0 = ModelHom.zero M M ∧ lift 1 = BialgHom.id R M.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) := by
  obtain ⟨M, f, hf, hM⟩ := exists_maximal_model_extension X
  obtain ⟨lift, hlift⟩ := exists_integral_scalar_action (F := F) f hf fun g ↦ (hM M g).exists
  exact ⟨M, f, lift, hf, hM, hlift⟩

/-- Construct the minimum with the actual prescribed scalar action and its laws. -/
theorem exists_minimal_model_scalar_action :
    ∃ (M : FF R K) (f : GenericGaloisHom X M) (lift : F → ModelHom M M),
      Function.Bijective f ∧
      (∀ (Y : FF R K) (g : GenericGaloisHom Y M), ∃! h : ModelHom Y M, genericHom h = g) ∧
      (∀ a x, genericHom (lift a) (f x) = f (a • x)) ∧
      lift 0 = ModelHom.zero M M ∧ lift 1 = BialgHom.id R M.CoordinateRing ∧
      (∀ a b, lift (a + b) = (lift a).add (lift b)) ∧
      (∀ a b, lift (a * b) = (lift b).comp (lift a)) := by
  obtain ⟨M, f, hf, hM⟩ := exists_minimal_model_extension X
  obtain ⟨lift, hlift⟩ := exists_integral_scalar_action (F := F) f hf fun g ↦ (hM M g).exists
  exact ⟨M, f, lift, hf, hM, hlift⟩

end ThreeAdicPlan
