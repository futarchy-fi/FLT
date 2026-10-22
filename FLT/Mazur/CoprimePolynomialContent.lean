/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.RingTheory.LocalProperties.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Exact contents of polynomials with comaximal coefficient ideals

Comaximality upgrades the usual radical comparison of polynomial contents
to equality of ideals over arbitrary rings. In particular, this retains
nilpotent coefficients when encoding disjoint endpoint equations.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.CoprimePolynomialContent
variable {R : Type*} [CommRing R]

/-- A polynomial whose coefficients generate the unit ideal cancels even over a nonreduced ring. -/
theorem cancel_zero_of_content_top (p q : R[X]) (hp : p.contentIdeal = ⊤)
    (hpq : p * q = 0) : q = 0 := by
  apply Polynomial.eq_zero_of_mul_eq_zero_of_smul p _ q hpq
  intro r hr
  have hcoeff (i : ℕ) : r * p.coeff i = 0 := by
    simpa only [coeff_smul, smul_eq_mul, coeff_zero] using congrArg (fun a ↦ a.coeff i) hr
  have hspan : ∀ x ∈ p.contentIdeal, r * x = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, _, rfl⟩ := Polynomial.mem_coeffs_iff.mp hx
      exact hcoeff i
    | zero => exact mul_zero r
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul a x _ hx => simp only [smul_eq_mul, mul_left_comm r a x, hx, mul_zero]
  simpa only [mul_one] using hspan 1 (by rw [hp]; trivial)

/-- A unit content factor preserves the other factor's exact coefficient ideal. -/
theorem content_mul_of_top (p q : R[X]) (hp : p.contentIdeal = ⊤) :
    (p * q).contentIdeal = q.contentIdeal := by
  apply le_antisymm
  · simpa only [hp, Ideal.top_mul] using p.contentIdeal_mul_le_mul_contentIdeal q
  · let K := (p * q).contentIdeal
    let f := Ideal.Quotient.mk K
    have hp' : (p.map f).contentIdeal = ⊤ := by
      rw [contentIdeal_map_eq_map_contentIdeal, hp, Ideal.map_top]
    have hprod : p.map f * q.map f = 0 := by
      rw [← Polynomial.map_mul, ← contentIdeal_eq_bot_iff,
        contentIdeal_map_eq_map_contentIdeal, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    have hq := cancel_zero_of_content_top (p.map f) (q.map f) hp' hprod
    have hcontent := (contentIdeal_eq_bot_iff _).mpr hq
    rw [contentIdeal_map_eq_map_contentIdeal, Ideal.map_eq_bot_iff_le_ker,
      Ideal.mk_ker] at hcontent
    exact hcontent

/-- Two comaximal coefficient ideals multiply exactly, without passing to radicals. -/
theorem content_mul_of_coprime (p q : R[X]) (h : IsCoprime p.contentIdeal q.contentIdeal) :
    (p * q).contentIdeal = p.contentIdeal * q.contentIdeal := by
  apply Ideal.eq_of_localization_maximal
  intro P hP
  let _ : P.IsMaximal := hP
  let f := algebraMap R (Localization.AtPrime P)
  change Ideal.map f _ = Ideal.map f _
  rw [Ideal.map_mul, ← contentIdeal_map_eq_map_contentIdeal,
    ← contentIdeal_map_eq_map_contentIdeal, ← contentIdeal_map_eq_map_contentIdeal,
    Polynomial.map_mul]
  have hnot : ¬ p.contentIdeal ≤ P ∨ ¬ q.contentIdeal ≤ P := by
    by_contra! hn
    have ht : (⊤ : Ideal R) ≤ P := by
      rw [← Ideal.isCoprime_iff_sup_eq.mp h]
      exact sup_le hn.1 hn.2
    exact hP.ne_top (top_le_iff.mp ht)
  rcases hnot with hp | hq
  · have ht : (p.map f).contentIdeal = ⊤ := by
      rw [contentIdeal_map_eq_map_contentIdeal]
      exact IsLocalization.AtPrime.map_eq_top_of_not_le _ hp
    rw [content_mul_of_top _ _ ht, ht, Ideal.top_mul]
  · have ht : (q.map f).contentIdeal = ⊤ := by
      rw [contentIdeal_map_eq_map_contentIdeal]
      exact IsLocalization.AtPrime.map_eq_top_of_not_le _ hq
    rw [mul_comm (p.map f), content_mul_of_top _ _ ht, ht, Ideal.mul_top]

/-- Pairwise comaximal coefficient ideals multiply exactly for every finite family. -/
theorem content_prod {I : Type*} (s : Finset I) (p : I → R[X])
    (h : (s : Set I).Pairwise fun i j ↦ IsCoprime (p i).contentIdeal (p j).contentIdeal) :
    (∏ i ∈ s, p i).contentIdeal = ∏ i ∈ s, (p i).contentIdeal := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hs := h.mono (Finset.subset_insert i s)
    rw [Finset.prod_insert hi, Finset.prod_insert hi, content_mul_of_coprime,
      ih hs]
    rw [ih hs]
    exact IsCoprime.prod_right fun j hj ↦ h (Finset.mem_insert_self i s)
      (Finset.mem_insert_of_mem hj) (fun he ↦ hi (he.symm ▸ hj))

end FLT.Mazur.CoprimePolynomialContent
