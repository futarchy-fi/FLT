/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.DividedPowers.Padic
public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# Descending rational divided powers from generators

An integral ideal in a subring of a rational algebra inherits divided powers
when the positive divided powers of its generators lift back into the ideal.
The proof extends generator integrality to all finite ideal expressions.
-/

@[expose] public noncomputable section
namespace DividedPowers
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ B]
  (f : A →+* B) (I : Ideal A)

/-- Ambient rational divided powers, including on elements outside a chosen ideal. -/
def rationalDpow : DividedPowers (⊤ : Ideal B) := by
  classical
  exact RatAlgebra.dividedPowers ⊤

/-- Positive divided powers integral on generators are integral on their entire ideal. -/
theorem rationalDpow_lift_span {S : Set A} (hI : I = Ideal.span S)
    (hS : ∀ n, n ≠ 0 → ∀ x ∈ S,
      ∃ y ∈ I, f y = (rationalDpow (B := B)).dpow n (f x))
    (n : ℕ) {x : A} (hx : x ∈ I) :
    ∃ y : A, (n ≠ 0 → y ∈ I) ∧ f y = (rationalDpow (B := B)).dpow n (f x) := by
  classical
  let d := rationalDpow (B := B)
  have hz : ∀ x : A, ∃ y : A, (0 ≠ 0 → y ∈ I) ∧ f y = d.dpow 0 (f x) := by
    intro x
    exact ⟨1, by simp, by rw [d.dpow_zero Submodule.mem_top, map_one]⟩
  rw [hI] at hx
  induction hx using Submodule.span_induction generalizing n with
  | mem x hx =>
      by_cases hn : n = 0
      · subst n; exact hz x
      · obtain ⟨y, hy, he⟩ := hS n hn x hx
        exact ⟨y, fun _ ↦ hy, he⟩
  | zero =>
      by_cases hn : n = 0
      · subst n; exact hz 0
      · exact ⟨0, fun _ ↦ I.zero_mem, by rw [map_zero, d.dpow_eval_zero hn]⟩
  | add x z hx hz' ihx ihz =>
      choose y hy he using ihx
      choose w hw hf using ihz
      refine ⟨∑ a ∈ Finset.antidiagonal n, y a.1 * w a.2, ?_, ?_⟩
      · intro hn
        apply I.sum_mem
        intro a ha
        by_cases h : a.1 = 0
        · have h' : a.2 ≠ 0 := by
            have := Finset.mem_antidiagonal.mp ha
            omega
          exact I.mul_mem_left _ (hw _ h')
        · exact I.mul_mem_right _ (hy _ h)
      · rw [map_sum, map_add, d.dpow_add Submodule.mem_top Submodule.mem_top]
        exact Finset.sum_congr rfl fun a _ ↦ by rw [map_mul, he, hf]
  | smul a x hx ih =>
      obtain ⟨y, hy, he⟩ := ih n
      refine ⟨a ^ n * y, fun hn ↦ I.mul_mem_left _ (hy hn), ?_⟩
      rw [map_mul, map_pow, he]
      rw [smul_eq_mul, map_mul]
      exact (d.dpow_mul (a := f a) (Submodule.mem_top : f x ∈ (⊤ : Ideal B))).symm

/-- Actual integral divided powers, constructed from the generator integrality proof. -/
def rationalDividedPowers (hf : Function.Injective f) {S : Set A}
    (hI : I = Ideal.span S)
    (hS : ∀ n, n ≠ 0 → ∀ x ∈ S,
      ∃ y ∈ I, f y = (rationalDpow (B := B)).dpow n (f x)) : DividedPowers I := by
  classical
  let J := I.map f
  let d : DividedPowers J := RatAlgebra.dividedPowers J
  apply DividedPowers.ofInjective I J f hf d rfl
  intro n x hx
  obtain ⟨y, hy, he⟩ := rationalDpow_lift_span f I hI hS n hx
  refine ⟨y, hy, he.trans ?_⟩
  simp only [rationalDpow, RatAlgebra.dpow_apply, Submodule.mem_top, ite_true, d]
  rw [ite_eq_left (Ideal.mem_map_of_mem f hx)]

/-- The integral operations retain the rational factorial formula after embedding. -/
theorem rationalDividedPowers_map (hf : Function.Injective f) {S : Set A}
    (hI : I = Ideal.span S)
    (hS : ∀ n, n ≠ 0 → ∀ x ∈ S,
      ∃ y ∈ I, f y = (rationalDpow (B := B)).dpow n (f x))
    (n : ℕ) {x : A} (hx : x ∈ I) :
    f ((rationalDividedPowers f I hf hI hS).dpow n x) =
      (rationalDpow (B := B)).dpow n (f x) := by
  classical
  apply (IsUnit.natCast_factorial_of_algebra ℚ n).mul_left_cancel
  calc
    (n.factorial : B) * f ((rationalDividedPowers f I hf hI hS).dpow n x) = f x ^ n := by
      simpa only [map_mul, map_natCast, map_pow] using congrArg f
        ((rationalDividedPowers f I hf hI hS).factorial_mul_dpow_eq_pow (n := n) hx)
    _ = _ := ((rationalDpow (B := B)).factorial_mul_dpow_eq_pow
      (Submodule.mem_top : f x ∈ (⊤ : Ideal B))).symm

end DividedPowers
