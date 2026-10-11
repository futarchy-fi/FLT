/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorComplementLeadingProduct

/-!
# Exact orders of powers and weighted monomials

At an integral one-point Cartier divisor, positive exact orders add and
multiply under actual function products and powers. The statements concern
the original function filtration, including zero exponents in mixed monomials.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {k : Type} [Field k] {X : Scheme} (f : X ⟶ Spec (.of k))
  {I : X.IdealSheafData} (hI : EffectiveCartier I)
  [IsIntegral I.subscheme] [Subsingleton I.subscheme]
include f

/-- Positive exact pole orders add, expressed independently of successor presentations. -/
theorem divisorPoleFunctions_mul_not_mem_pred
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {a b : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (ha : a ∈ divisorPoleFunctions hI m) (hb : b ∈ divisorPoleFunctions hI n)
    (ha' : a ∉ divisorPoleFunctions hI (m - 1))
    (hb' : b ∉ divisorPoleFunctions hI (n - 1)) :
    a * b ∉ divisorPoleFunctions hI (m + n - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  have he : m + 1 + (n + 1) - 1 = m + n + 1 := by omega
  rw [he]
  exact divisorPoleFunctions_mul_not_mem f hI m n ha hb ha' hb'

/-- Every positive power has its exact multiplied pole order. -/
theorem divisorPoleFunctions_pow_not_mem
    (m : ℕ) (hm : 0 < m)
    {a : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (ha : a ∈ divisorPoleFunctions hI m)
    (ha' : a ∉ divisorPoleFunctions hI (m - 1)) (r : ℕ) (hr : 0 < r) :
    a ^ r ∉ divisorPoleFunctions hI (m * r - 1) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hr)
  clear hr
  induction r with
  | zero => simpa only [Nat.zero_add, pow_one, Nat.mul_one] using ha'
  | succ r ih =>
    have hp := divisorPoleFunctions_mul_not_mem_pred f hI (m * (r + 1)) m
      (Nat.mul_pos hm (by omega)) hm (divisorPoleFunctions_pow hI ha (r + 1)) ha ih ha'
    simpa only [pow_succ, Nat.mul_succ] using hp

/-- A nonconstant monomial has exactly its weighted order in the original pole filtration. -/
theorem divisorPoleFunctions_monomial_not_mem
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {x y : Γ(Scheme.Opens.toScheme (X := X) I.support.compl, ⊤)}
    (hx : x ∈ divisorPoleFunctions hI m) (hy : y ∈ divisorPoleFunctions hI n)
    (hx' : x ∉ divisorPoleFunctions hI (m - 1))
    (hy' : y ∉ divisorPoleFunctions hI (n - 1)) (a b : ℕ) (hab : 0 < a + b) :
    x ^ a * y ^ b ∉ divisorPoleFunctions hI (m * a + n * b - 1) := by
  by_cases ha : a = 0
  · subst a
    simpa only [pow_zero, one_mul, Nat.mul_zero, Nat.zero_add] using
      divisorPoleFunctions_pow_not_mem f hI n hn hy hy' b (by omega)
  by_cases hb : b = 0
  · subst b
    simpa only [pow_zero, mul_one, Nat.mul_zero, Nat.add_zero] using
      divisorPoleFunctions_pow_not_mem f hI m hm hx hx' a (by omega)
  exact divisorPoleFunctions_mul_not_mem_pred f hI (m * a) (n * b)
    (Nat.mul_pos hm (by omega)) (Nat.mul_pos hn (by omega))
    (divisorPoleFunctions_pow hI hx a) (divisorPoleFunctions_pow hI hy b)
    (divisorPoleFunctions_pow_not_mem f hI m hm hx hx' a (by omega))
    (divisorPoleFunctions_pow_not_mem f hI n hn hy hy' b (by omega))

end FLT.Mazur.FCurve
