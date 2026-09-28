/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsor
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.RingTheory.TensorProduct.Free

/-!
# Freeness after tensoring a Hopf inclusion with its target

Over a field, the relative torsor isomorphism makes `A ⊗[B] A` free over
the left factor `A`, with rank the dimension of the augmentation quotient.
This does not yet descend freeness to `A` over `B`.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k B] [Algebra B A] [IsScalarTower k B A]

/-- Over a field, the relative tensor square of a commutative Hopf algebra
is free over its left factor. -/
theorem free_selfTensorProduct (f : B →ₐc[k] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom k B A) : Module.Free A (A ⊗[B] A) :=
  Module.Free.of_equiv (torsorEquiv f hf).symm.toLinearEquiv

/-- The rank of the relative tensor square is the dimension of the
augmentation quotient over the original field. -/
theorem finrank_selfTensorProduct (f : B →ₐc[k] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom k B A) :
    Module.finrank A (A ⊗[B] A) = Module.finrank k (A ⧸ augmentationIdeal f) := by
  let : Nontrivial A := (Bialgebra.counitAlgHom k A).domain_nontrivial
  rw [(torsorEquiv f hf).toLinearEquiv.finrank_eq, Module.finrank_baseChange]

end HopfAlgebra
