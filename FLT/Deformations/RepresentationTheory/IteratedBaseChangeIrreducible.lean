/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Irreducibility and iterated coefficient extension

The canonical cancellation of iterated base change intertwines the actual
operators. This permits descent from an algebraic closure after any extension.
-/

@[expose] public noncomputable section
open scoped TensorProduct MonoidAlgebra
namespace Representation

variable {k G V W : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]

/-- An equivariant linear equivalence preserves irreducibility. -/
theorem Equiv.isIrreducible_iff {ρ : Representation k G V} {σ : Representation k G W}
    (e : ρ.Equiv σ) : ρ.IsIrreducible ↔ σ.IsIrreducible := by
  rw [irreducible_iff_isSimpleModule_asModule, irreducible_iff_isSimpleModule_asModule]
  let f := IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap
  exact LinearMap.isSimpleModule_iff_of_bijective (l := f) e.toLinearEquiv.bijective

/-- Canceling iterated coefficient extension preserves irreducibility of the actual action. -/
theorem isIrreducible_baseChange_tower_iff (ρ : Representation k G V)
    (E L : Type*) [Field E] [Field L] [Algebra k E] [Algebra k L] [Algebra E L]
    [IsScalarTower k E L] :
    (baseChange L (baseChange E ρ)).IsIrreducible ↔ (baseChange L ρ).IsIrreducible := by
  let e := _root_.TensorProduct.AlgebraTensorModule.cancelBaseChange k E L L V
  apply Equiv.isIrreducible_iff (Equiv.mk e ?_)
  intro g
  apply LinearMap.ext
  intro x
  change e (((ρ g).baseChange E).baseChange L x) = (ρ g).baseChange L (e x)
  rw [LinearMap.baseChange_baseChange]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, e]

end Representation
