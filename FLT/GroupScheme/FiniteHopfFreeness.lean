/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HopfTorsorFree
public import FLT.GroupScheme.SemilocalFreeDescent
public import Mathlib.RingTheory.Artinian.Module

/-!
# Finite commutative Hopf algebras are free over Hopf subalgebras

The torsor isomorphism trivializes the relative tensor square. Freeness
then descends along the injective finite extension of semilocal rings.
-/

@[expose] public noncomputable section

namespace HopfAlgebra

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B]
  [HopfAlgebra k A] [HopfAlgebra k B] [Algebra B A] [IsScalarTower k B A]

/-- A finite commutative Hopf algebra over a field is free over every Hopf
subalgebra, expressed by an injective bialgebra map compatible with its scalar action. -/
theorem free_of_injective_bialgHom [Module.Finite k A] (f : B →ₐc[k] A)
    (hf : f.toAlgHom = IsScalarTower.toAlgHom k B A) (hinj : Function.Injective f) :
    Module.Free B A := by
  let : Nontrivial A := (Bialgebra.counitAlgHom k A).domain_nontrivial
  let : Module.Finite k B := Module.Finite.of_injective f.toLinearMap hinj
  let : IsArtinianRing B := IsArtinianRing.of_finite k B
  let : Module.Finite B A := Module.Finite.of_restrictScalars_finite k B A
  let : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr (by
    have h : ⇑f = algebraMap B A := congrArg DFunLike.coe hf
    rwa [← h])
  let : Module.Free A (TensorProduct B A A) := free_selfTensorProduct f hf
  exact Module.free_of_free_baseChange_of_integral A

end HopfAlgebra
