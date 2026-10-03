/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCyclicMonomialReduction
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Digit monomials span polynomial images

Total-degree reduction applies to each term of a polynomial. Consequently
a generated algebra with cyclic degree-p relations is spanned by p^r
explicit monomials when it has r generators.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan.CyclicPresentation

variable {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] (x : ι → A) (p : ℕ)
  (hp : 1 < p) (next : ι → ι) (a : ι → R)
  (hrel : ∀ i, x i ^ p = a i • x (next i))

include hp hrel in
/-- Every polynomial evaluated at the cyclic coordinates lies in the digit span. -/
theorem aeval_mem_digitSpan (f : MvPolynomial ι R) :
    MvPolynomial.aeval x f ∈ digitSpan (R := R) x p := by
  induction f using MvPolynomial.induction_on' with
  | monomial d r =>
    rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun _ ↦ pow_zero _)]
    rw [← Algebra.smul_def]
    change r • monomial x d ∈ digitSpan (R := R) x p
    exact (digitSpan (R := R) x p).smul_mem r (monomial_mem_digitSpan x p hp next a hrel d)
  | add f g hf hg =>
    rw [map_add]
    exact (digitSpan (R := R) x p).add_mem hf hg

include hp hrel in
/-- Surjective polynomial evaluation makes the digit monomials span the entire algebra. -/
theorem digitSpan_eq_top (hsurj : Function.Surjective (MvPolynomial.aeval (R := R) x)) :
    digitSpan (R := R) x p = ⊤ := by
  apply top_unique
  intro y hy
  obtain ⟨f, rfl⟩ := hsurj y
  exact aeval_mem_digitSpan x p hp next a hrel f

end ThreeAdicPlan.CyclicPresentation
