/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudIntegralClosureBound
public import FLT.GroupScheme.RaynaudModelUpperBound

/-!
# Existence of a maximal finite flat model

Integral coordinate images are bounded inside a finite integral closure.
The ascending-chain condition gives a maximal image, and graph upper bounds
make it greatest. Its witness is an actual finite flat model.
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u
namespace ThreeAdicPlan

variable {R K : Type u} [CommRing R] [Field K] [Algebra R K] [PerfectField K]

/-- The integral coordinate image, viewed as a submodule of its finite ambient bound. -/
def GenericGaloisHom.integralCoordinateLattice {X Y : FF R K} (f : GenericGaloisHom X Y) :
    Submodule R (integralClosure R (K ⊗[R] X.CoordinateRing)) :=
  f.integralCoordinateImage.toSubmodule.comap (integralClosure R _).val.toLinearMap

/-- Passing to the ambient integral closure preserves and reflects coordinate inclusion. -/
theorem GenericGaloisHom.integralCoordinateLattice_le_iff {X Y Z : FF R K}
    (f : GenericGaloisHom X Y) (g : GenericGaloisHom X Z) :
    f.integralCoordinateLattice ≤ g.integralCoordinateLattice ↔
      f.integralCoordinateImage ≤ g.integralCoordinateImage := by
  constructor
  · intro h x hx
    exact h (show (⟨x, f.integralCoordinateImage_le_integralClosure hx⟩ :
      integralClosure R (K ⊗[R] X.CoordinateRing)) ∈ f.integralCoordinateLattice from hx)
  · intro h x hx
    exact h hx

variable [IsDedekindDomain R] [IsFractionRing R K]

/-- Construct a greatest coordinate image among all models of a fixed generic fibre.
The proof uses no ramification bound or coordinate presentation. -/
theorem exists_maximal_model (X : FF R K) :
    ∃ (M : FF R K) (f : GenericGaloisHom X M), Function.Bijective f ∧
      ∀ (Y : FF R K) (g : GenericGaloisHom X Y),
        g.integralCoordinateImage ≤ f.integralCoordinateImage := by
  let : Module.Finite R (integralClosure R (K ⊗[R] X.CoordinateRing)) :=
    RaynaudParameters.finite_integralClosure_of_etale R K _
  let C : Set (Submodule R (integralClosure R (K ⊗[R] X.CoordinateRing))) :=
    {L | ∃ (Y : FF R K) (f : GenericGaloisHom X Y),
      Function.Bijective f ∧ L = f.integralCoordinateLattice}
  let idX : GenericGaloisHom X X :=
    { toFun := id, map_zero' := rfl, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  have hC : C.Nonempty := ⟨idX.integralCoordinateLattice, X, idX, Function.bijective_id, rfl⟩
  obtain ⟨L, ⟨M, f, hf, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian R (integralClosure R (K ⊗[R] X.CoordinateRing))) C hC
  refine ⟨M, f, hf, fun Y g ↦ ?_⟩
  obtain ⟨W, k, hk, -, -, hfk, hgk⟩ := exists_common_model_coordinate_upper_bound f hf g
  have hle := (f.integralCoordinateLattice_le_iff k).mpr hfk
  have heq : f.integralCoordinateLattice = k.integralCoordinateLattice := by
    apply le_antisymm hle
    by_contra h
    exact hmax _ ⟨W, k, hk, rfl⟩ (lt_of_le_not_ge hle h)
  apply (g.integralCoordinateLattice_le_iff f).mp
  rw [heq]
  exact (g.integralCoordinateLattice_le_iff k).mpr hgk

end ThreeAdicPlan
