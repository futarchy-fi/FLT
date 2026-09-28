/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Transporting freeness between quotient fibres and base change
-/

@[expose] public noncomputable section

open scoped TensorProduct
open Algebra.TensorProduct

namespace Algebra

variable {R B A : Type*} [CommRing R] [CommRing B] [CommRing A]
  [Algebra R B] [Algebra R A] [Algebra B A] [IsScalarTower R B A]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The quotient of `B` by an extended ideal is the base change of `B`
to the corresponding quotient of `R`. -/
def quotientBaseChangeEquiv (I : Ideal R) :
    (B ⧸ I.map (algebraMap R B)) ≃ₐ[B] (R ⧸ I) ⊗[R] B :=
  (quotIdealMapEquivTensorQuot B I).trans (commRight R B (R ⧸ I))

@[simp]
theorem quotientBaseChangeEquiv_mk (I : Ideal R) (b : B) :
    quotientBaseChangeEquiv (B := B) I (Ideal.Quotient.mk (I.map (algebraMap R B)) b) =
      1 ⊗ₜ[R] b := by
  simp [quotientBaseChangeEquiv]

/-- Taking the fibre over the quotient of `B` agrees with base change from `R`. -/
def quotientFiberEquiv (I : Ideal R) :
    (B ⧸ I.map (algebraMap R B)) ⊗[B] A ≃ₐ[R] (R ⧸ I) ⊗[R] A :=
  ((Algebra.TensorProduct.comm B (B ⧸ I.map (algebraMap R B)) A).restrictScalars R).trans
    ((((Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A)
      (quotIdealMapEquivTensorQuot B I)).trans
      (cancelBaseChange R B A A (R ⧸ I))).restrictScalars R).trans
      (Algebra.TensorProduct.comm R A (R ⧸ I)))

@[simp]
theorem quotientFiberEquiv_mk_tmul (I : Ideal R) (b : B) (a : A) :
    quotientFiberEquiv (A := A) I (Ideal.Quotient.mk (I.map (algebraMap R B)) b ⊗ₜ[B] a) =
      1 ⊗ₜ[R] (b • a) := by
  simp [quotientFiberEquiv]

/-- Freeness of the base-changed algebra descends through the canonical
identification of its coefficient ring with the quotient of `B`. -/
theorem free_quotientFiber_of_free_baseChange (I : Ideal R)
    (hfree : letI :=
      (Algebra.TensorProduct.map (AlgHom.id R (R ⧸ I))
        (IsScalarTower.toAlgHom R B A)).toAlgebra
      Module.Free ((R ⧸ I) ⊗[R] B) ((R ⧸ I) ⊗[R] A)) :
    Module.Free (B ⧸ I.map (algebraMap R B))
      ((B ⧸ I.map (algebraMap R B)) ⊗[B] A) := by
  let := (Algebra.TensorProduct.map (AlgHom.id R (R ⧸ I))
    (IsScalarTower.toAlgHom R B A)).toAlgebra
  let := hfree
  let eB := (quotientBaseChangeEquiv (B := B) I).toRingEquiv
  let := RingHomInvPair.of_ringEquiv eB
  let := RingHomInvPair.of_ringEquiv_symm eB
  let eA := quotientFiberEquiv (B := B) (A := A) I
  let e : ((B ⧸ I.map (algebraMap R B)) ⊗[B] A) ≃ₛₗ[
      (eB : (B ⧸ I.map (algebraMap R B)) →+* (R ⧸ I) ⊗[R] B)]
      (R ⧸ I) ⊗[R] A := by
    refine { __ := eA.toAddEquiv, map_smul' := ?_ }
    intro b x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.map (algebraMap R B)) b
    change eA ((Ideal.Quotient.mk (I.map (algebraMap R B)) b) • x) =
      eB (Ideal.Quotient.mk (I.map (algebraMap R B)) b) • eA x
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
    change eA (Ideal.Quotient.mk (I.map (algebraMap R B)) b ⊗ₜ[B] 1) =
      Algebra.TensorProduct.map (AlgHom.id R (R ⧸ I))
        (IsScalarTower.toAlgHom R B A) (eB (Ideal.Quotient.mk (I.map (algebraMap R B)) b))
    simp [eA, eB, Algebra.smul_def]
  exact Module.Free.of_equiv e.symm

end Algebra
