/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Deformations.RepresentationTheory.TorsionTensorMaps
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Cardinality of the original p-power levels

A finite basis identifies scalar extension with a finite product, including
level zero. Applying this twice computes the original coefficient-tensor level.
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace GaloisRepresentation.PrimePower

/-- A finite free module has the expected number of points after scalar extension. -/
theorem card_baseChange {A S M : Type*} [CommRing A] [Nontrivial A]
    [CommRing S] [Algebra A S] [AddCommGroup M] [Module A M]
    [Module.Finite A M] [Module.Free A M] :
    Nat.card (S ⊗[A] M) = Nat.card S ^ Module.finrank A M := by
  classical
  let b := Module.finBasis A M
  rw [Nat.card_congr (b.baseChange S).equivFun.toEquiv, Nat.card_fun, Nat.card_fin]

/-- The p-adic coefficient quotient has p^n elements, also for n = 0. -/
theorem card_padic_quotient (p n : ℕ) [Fact p.Prime] :
    Nat.card (Quot (p : ℤ_[p]) n) = p ^ n := by
  have h := Nat.card_congr (RingHom.quotientKerEquivOfSurjective
    (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) n))).toEquiv
  rw [PadicInt.ker_toZModPow] at h
  exact h.trans (Nat.card_zmod _)

/-- A finite free coefficient algebra retains its original p-adic degree. -/
theorem card_coefficient_quotient (p n : ℕ) [Fact p.Prime]
    (R : Type*) [CommRing R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R] :
    Nat.card (Quot (p : R) n) = p ^ (n * Module.finrank ℤ_[p] R) := by
  have he := Nat.card_congr (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R
    (Ideal.span {(p : ℤ_[p]) ^ n})).toEquiv
  simp only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast] at he
  rw [he, card_baseChange, card_padic_quotient, ← pow_mul]

/-- Cardinality of the actual quotient tensor module, without changing coefficients. -/
theorem card_level (p n : ℕ) [Fact p.Prime]
    (R V : Type*) [CommRing R] [Nontrivial R] [Algebra ℤ_[p] R]
    [Module.Finite ℤ_[p] R] [Module.Free ℤ_[p] R]
    [AddCommGroup V] [Module R V] [Module.Finite R V] [Module.Free R V] :
    Nat.card (Level (V := V) (p : R) n) =
      p ^ (n * (Module.finrank ℤ_[p] R * Module.finrank R V)) := by
  rw [card_baseChange, card_coefficient_quotient, ← pow_mul, Nat.mul_assoc]

end GaloisRepresentation.PrimePower
