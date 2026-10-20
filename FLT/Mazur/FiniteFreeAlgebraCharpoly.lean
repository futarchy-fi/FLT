/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Characteristic equations for finite free algebras

An actual finite basis supplies a monic annihilating polynomial. Its
coefficients commute with arbitrary scalar extension and algebra transport.
-/

@[expose] public noncomputable section
open Module TensorProduct Polynomial
namespace FLT.Mazur.FiniteFreeAlgebraCharpoly
variable {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {ι κ : Type*} [Finite ι] [Finite κ]
  (b : Basis ι R B)

/-- The characteristic polynomial of multiplication in the displayed finite algebra. -/
def charpoly (x : B) : R[X] :=
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  (Algebra.lmul R B x).charpoly

/-- The equation is monic, including over rings with nilpotents. -/
theorem monic (x : B) : (charpoly b x).Monic := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  exact LinearMap.charpoly_monic _

/-- Cayley-Hamilton annihilates the original element. -/
theorem aeval_eq_zero (x : B) : aeval x (charpoly b x) = 0 := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  exact Algebra.aeval_self_charpoly_lmul x

/-- Transport permits independent bases on both presentations of the algebra. -/
theorem transport (c : Basis κ R C) (e : B ≃ₐ[R] C) (x : B) :
    charpoly c (e x) = charpoly b x := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  let _ := Module.Free.of_basis c
  let _ := Module.Finite.of_basis c
  have h : e.toLinearEquiv.conj (Algebra.lmul R B x) = Algebra.lmul R C (e x) := by
    ext y
    change e (x * e.symm y) = e x * y
    rw [map_mul, e.apply_symm_apply]
  change (Algebra.lmul R C (e x)).charpoly = (Algebra.lmul R B x).charpoly
  rw [← h, LinearEquiv.charpoly_conj]

variable (S : Type*) [CommRing S] [Algebra R S]

/-- No flatness assumption is needed to change the coefficients of the equation. -/
theorem baseChange (x : B) :
    charpoly (b.baseChange S) (1 ⊗ₜ[R] x) = (charpoly b x).map (algebraMap R S) := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  change (Algebra.lmul S (S ⊗[R] B) (1 ⊗ₜ[R] x)).charpoly = _
  rw [← Algebra.baseChange_lmul, LinearMap.charpoly_baseChange]
  rfl

end FLT.Mazur.FiniteFreeAlgebraCharpoly
