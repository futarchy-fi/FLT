/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfFreeness
public import FLT.GroupScheme.QuotientFiberFreeness
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Freeness of a Hopf inclusion on a residue fibre
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
  [HopfAlgebra R B] [HopfAlgebra R A] [Algebra B A] [IsScalarTower R B A]

/-- An inclusion of finite commutative Hopf algebras that remains injective
on a residue fibre gives a free relative module on that fibre. -/
theorem free_quotientFiber_of_injective_baseChange [Module.Finite R A]
    (f : B →ₐc[R] A) (hf : f.toAlgHom = IsScalarTower.toAlgHom R B A)
    (I : Ideal R) [I.IsMaximal]
    (hinj : Function.Injective
      (Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) f)) :
    Module.Free (B ⧸ I.map (algebraMap R B))
      ((B ⧸ I.map (algebraMap R B)) ⊗[B] A) := by
  let := @Ideal.Quotient.field
  apply Algebra.free_quotientFiber_of_free_baseChange I
  rw [← hf]
  let F := Bialgebra.TensorProduct.map (BialgHom.id (R ⧸ I) (R ⧸ I)) f
  let := (Algebra.TensorProduct.map (AlgHom.id R (R ⧸ I)) f.toAlgHom).toAlgebra
  let : IsScalarTower (R ⧸ I) ((R ⧸ I) ⊗[R] B) ((R ⧸ I) ⊗[R] A) := by
    apply IsScalarTower.of_algebraMap_eq
    intro r
    exact (F.toAlgHom.commutes r).symm
  exact free_of_injective_bialgHom F (by ext; rfl) hinj

end HopfAlgebra
