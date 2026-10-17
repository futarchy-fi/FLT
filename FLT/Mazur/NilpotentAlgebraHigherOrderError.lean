/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.NilpotentAlgebraAutomorphism

/-!
# Higher-order coefficient errors on arbitrary algebras

An error in the r-th coefficient-ideal power raises the k-th power to the
(k+r)-th power. The argument is base-linear and does not truncate Laurent
support. Inverse and composed automorphisms retain the same error order.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.NilpotentAlgebraHigherOrderError
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (I : Ideal R) (r : ℕ) (f : A →ₐ[R] A)
  (hf : ∀ x, f x - x ∈ (I.map (algebraMap R A)) ^ r)
local notation "J" => Ideal.map (algebraMap R A) I

include hf in
/-- An r-th order error raises every coefficient power by r. -/
theorem error_mem_power (k : ℕ) (x : A) (hx : x ∈ J ^ k) :
    f x - x ∈ J ^ (k + r) := by
  rw [← Ideal.map_pow] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, _, rfl⟩ := hx
    simp only [AlgHom.commutes, sub_self, Submodule.zero_mem]
  | zero => simp
  | add x y _ _ hx hy =>
    convert (J ^ (k + r)).add_mem hx hy using 1
    simp only [map_add]
    ring
  | smul c x hx ih =>
    change f (c * x) - c * x ∈ J ^ (k + r)
    have hx' : x ∈ J ^ k := by rwa [← Ideal.map_pow]
    have h := Ideal.mul_mem_mul hx' (hf c)
    rw [← pow_add] at h
    convert (J ^ (k + r)).add_mem ((J ^ (k + r)).mul_mem_left (f c) ih) h using 1
    rw [map_mul]
    ring

/-- Inverting a full algebra equivalence preserves the error order on every input. -/
theorem symm_sub_mem (a : A ≃ₐ[R] A)
    (ha : ∀ x, a x - x ∈ J ^ r) (x : A) : a.symm x - x ∈ J ^ r := by
  have h := (J ^ r).neg_mem (ha (a.symm x))
  simpa only [AlgEquiv.apply_symm_apply, neg_sub] using h

include hf in
/-- Composition retains the shared higher coefficient-error order. -/
theorem comp_sub_mem (g : A →ₐ[R] A)
    (hg : ∀ x, g x - x ∈ J ^ r) (x : A) : (f.comp g) x - x ∈ J ^ r := by
  have h := (J ^ r).add_mem (hf (g x)) (hg x)
  simpa only [AlgHom.comp_apply, sub_add_sub_cancel] using h

end FLT.Mazur.NilpotentAlgebraHigherOrderError
