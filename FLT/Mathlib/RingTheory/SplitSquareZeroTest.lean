/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.TrivSqZeroExt.Ideal
public import Mathlib.RingTheory.Nilpotent.Basic

/-! # Split square-zero test algebras and their specified kernels -/

@[expose] public noncomputable section
namespace SplitSquareZeroTest
variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
  [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- Use the commutative module action as the right action in a split test algebra. -/
scoped instance rightModule : Module Sᵐᵒᵖ M :=
  Module.compHom _ ((RingHom.id S).fromOpposite mul_comm)
/-- Both actions agree. -/
scoped instance centralScalar : IsCentralScalar S M := ⟨fun _ _ ↦ rfl⟩
/-- Restricting scalars preserves the chosen right action. -/
scoped instance rightTower : IsScalarTower R Sᵐᵒᵖ M :=
  ⟨fun r s x ↦ smul_assoc r s.unop x⟩

open TrivSqZeroExt

/-- The augmentation kernel of the split extension is its original module. -/
def kernelEquiv : RingHom.ker (fstHom R S M) ≃ₗ[R] M where
  toFun x := x.val.snd
  invFun m := ⟨inr m, rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact TrivSqZeroExt.ext x.property.symm rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The specified reduction kernel has square zero. -/
theorem kernel_sq : RingHom.ker (fstHom R S M) ^ 2 = ⊥ :=
  kerIdeal_sq S M

/-- The induced algebra map is surjective exactly when the module map is. -/
theorem map_surjective (f : M →ₗ[S] N) (hf : Function.Surjective f) :
    Function.Surjective (TrivSqZeroExt.map f) := by
  intro x
  obtain ⟨m, hm⟩ := hf x.snd
  refine ⟨⟨x.fst, m⟩, TrivSqZeroExt.ext ?_ ?_⟩
  · exact fst_map f _
  · exact (snd_map f _).trans hm

/-- The kernel of the induced algebra map also has square zero. -/
theorem map_kernel_sq (f : M →ₗ[S] N) : RingHom.ker (TrivSqZeroExt.map f) ^ 2 = ⊥ := by
  apply le_antisymm _ bot_le
  calc
    _ ≤ kerIdeal S M ^ 2 := pow_le_pow_left' (fun x hx ↦ by
      change x.fst = 0
      simpa using congrArg TrivSqZeroExt.fst hx) 2
    _ = ⊥ := kerIdeal_sq S M

/-- Nilpotence of a natural-number scalar passes to the split extension. -/
theorem natCast_nilpotent (p : ℕ) (hp : IsNilpotent (p : S)) :
    IsNilpotent (p : TrivSqZeroExt S M) := by
  simpa using hp.map (inlHom S M)

end SplitSquareZeroTest
