/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentIdealContraction
public import FLT.Mazur.NilpotentPolynomialInverseBaseChange

/-!
# Algebra automorphisms congruent to the identity modulo a nilpotent base ideal

The inverse is obtained by finite contraction. No finite generation of the
algebra, flatness, or reducedness is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentAlgebraAutomorphism
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (f : A →ₐ[R] A)
  (hf : ∀ x, f x - x ∈ I.map (algebraMap R A))
local notation "J" => I.map (algebraMap R A)

include hf in
/-- A base-linear endomorphism's error raises the coefficient-ideal filtration. -/
theorem error_mem_power (n : ℕ) (x : A) (hx : x ∈ J ^ n) :
    f x - x ∈ J ^ (n + 1) := by
  rw [← Ideal.map_pow] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, _, rfl⟩ := hx
    simp only [AlgHom.commutes, sub_self, Submodule.zero_mem]
  | zero => simp
  | add x y _ _ hx hy =>
    convert (J ^ (n + 1)).add_mem hx hy using 1
    simp only [map_add]
    ring
  | smul c x hx ih =>
    change f (c * x) - c * x ∈ J ^ (n + 1)
    have hx' : x ∈ J ^ n := by rwa [← Ideal.map_pow]
    have h := Ideal.mul_mem_mul (hf c) hx'
    rw [← pow_succ'] at h
    convert (J ^ (n + 1)).add_mem ((J ^ (n + 1)).mul_mem_left (f c) ih) h using 1
    rw [map_mul]
    ring

include hf in
/-- The correction for an arbitrary target is a strict nilpotent-ideal contraction. -/
theorem correction_contracts (b : A) (n : ℕ) (x y : A) (hxy : x - y ∈ J ^ n) :
    (b + x - f x) - (b + y - f y) ∈ J ^ (n + 1) := by
  have h := (J ^ (n + 1)).neg_mem (error_mem_power I f hf n (x - y) hxy)
  convert h using 1
  rw [map_sub]
  ring

variable (hI : IsNilpotent I)

include hf hI in
/-- Finite correction solves every equation for the original algebra endomorphism. -/
theorem bijective : Function.Bijective f := by
  have hJ := NilpotentPolynomialInverse.mapIdeal_nilpotent I hI (algebraMap R A)
  constructor
  · intro x y hxy
    apply NilpotentIdealContraction.fixedPoint_unique J hJ (fun z ↦ f x + z - f z)
      (correction_contracts I f hf (f x))
    · abel
    · rw [hxy]
      abel
  · intro b
    obtain ⟨x, hx⟩ := NilpotentIdealContraction.exists_fixedPoint J hJ
      (fun z ↦ b + z - f z) (correction_contracts I f hf b)
    exact ⟨x, by linear_combination -hx⟩

/-- The full algebra automorphism, retaining every nilpotent correction. -/
def equiv : A ≃ₐ[R] A := AlgEquiv.ofBijective f (bijective I f hf hI)

/-- The constructed automorphism has exactly the specified forward map. -/
theorem equiv_toAlgHom : (equiv I f hf hI).toAlgHom = f := rfl

end FLT.Mazur.NilpotentAlgebraAutomorphism
