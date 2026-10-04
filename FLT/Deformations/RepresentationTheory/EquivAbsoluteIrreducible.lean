/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.IteratedBaseChangeIrreducible

/-! # Absolute irreducibility under an equivariant change of coordinates -/

@[expose] public noncomputable section
universe u
open scoped TensorProduct
namespace Representation

variable {k G V W : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {ρ : Representation k G V} {σ : Representation k G W}

/-- Scalar extension of an actual intertwining equivalence. -/
def Equiv.extendScalars (e : ρ.Equiv σ) (L : Type*) [Field L] [Algebra k L] :
    (baseChange L ρ).Equiv (baseChange L σ) := by
  refine Equiv.mk (e.toLinearEquiv.baseChange k L V W) ?_
  intro g
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul a v =>
    change a ⊗ₜ[k] e (ρ g v) = a ⊗ₜ[k] σ g (e v)
    exact congrArg (fun w ↦ a ⊗ₜ[k] w)
      (LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' g) v)
  | add x y hx hy => simp_all

/-- Coordinate transport works in every universe of coefficient extensions. -/
theorem Equiv.isAbsolutelyIrreducible_iff (e : ρ.Equiv σ) :
    ρ.IsAbsolutelyIrreducible.{u} ↔ σ.IsAbsolutelyIrreducible.{u} := by
  constructor <;> intro h <;> constructor <;> intro L _ _
  · exact (e.extendScalars L).isIrreducible_iff.mp (h.absolutelyIrreducible L _ _)
  · exact (e.extendScalars L).isIrreducible_iff.mpr (h.absolutelyIrreducible L _ _)

end Representation
