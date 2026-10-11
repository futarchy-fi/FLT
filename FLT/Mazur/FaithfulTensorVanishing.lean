/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Descending vanishing through two compatible scalar extensions

An identification after extension to a model ring detects vanishing after
another base change when a common overring is faithfully flat over that base.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FaithfulTensorVanishing

open TensorProduct

variable {A B D S : Type*} [CommRing A] [CommRing B] [CommRing D] [CommRing S]
  [Algebra A B] [Algebra A D] [Algebra A S] [Algebra B S] [Algebra D S]
  [IsScalarTower A B S] [IsScalarTower A D S] [Module.FaithfullyFlat B S]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module D N]
  (e : (D ⊗[A] M) ≃ₗ[D] N)

/-- The two scalar extensions agree over the common overring. -/
def equiv : (S ⊗[B] (B ⊗[A] M)) ≃ₗ[S] (S ⊗[D] N) :=
  AlgebraTensorModule.cancelBaseChange A B S S M ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A D S S M).symm ≪≫ₗ e.baseChange D S _ _

include e in
/-- Vanishing over the common overring descends to the original base-changed module. -/
theorem subsingleton [Subsingleton (S ⊗[D] N)] : Subsingleton (B ⊗[A] M) := by
  let _ := (equiv (B := B) (S := S) e).subsingleton
  exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right B S).mp inferInstance

include e in
/-- Flatness over the common overring descends to the original base-changed module. -/
theorem flat [Module.Flat S (S ⊗[D] N)] : Module.Flat B (B ⊗[A] M) := by
  let _ := Module.Flat.of_linearEquiv (equiv (B := B) (S := S) e)
  exact Module.Flat.of_flat_tensorProduct B (B ⊗[A] M) S

end FLT.Mazur.FaithfulTensorVanishing
