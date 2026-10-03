/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic

/-! # Reflecting units through maps with adically small kernels -/

@[expose] public noncomputable section
namespace PadicHodgeTheory

/-- A surjective map with kernel in an ideal of completeness reflects units. -/
theorem isUnit_of_adic_image {R S : Type*} [CommRing R] [CommRing S]
    (I : Ideal R) [IsAdicComplete I R] (f : R →+* S) (hf : Function.Surjective f)
    (hk : RingHom.ker f ≤ I) (x : R) (hx : IsUnit (f x)) : IsUnit x := by
  obtain ⟨u, hu⟩ := hx
  obtain ⟨y, hy⟩ := hf (↑u⁻¹ : S)
  have hxy : x * y - 1 ∈ RingHom.ker f := by
    change f (x * y - 1) = 0
    rw [map_sub, map_mul, map_one, ← hu, hy, Units.mul_inv, sub_self]
  exact isUnit_of_mul_isUnit_left
    (Ideal.isUnit_of_sub_one_mem_jacobson_bot (x * y)
      (IsAdicComplete.le_jacobson_bot I (hk hxy)))

/-- In an adically complete ring, reduction by the ideal reflects units. -/
theorem isUnit_of_adic_quotient {R : Type*} [CommRing R]
    (I : Ideal R) [IsAdicComplete I R] (x : R)
    (hx : IsUnit (Ideal.Quotient.mk I x)) : IsUnit x :=
  isUnit_of_adic_image I (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    (by intro y hy; exact Ideal.Quotient.eq_zero_iff_mem.mp hy) x hx

end PadicHodgeTheory
