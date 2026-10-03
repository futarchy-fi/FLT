/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.AdicRegularCancellation
public import Mathlib.RingTheory.AdicCompletion.Topology

/-! # Closed principal ideals from regular reduction and adic completeness -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable {R : Type*} [CommRing R] [IsDomain R]

/-- Arbitrarily precise divisibility approximations lift to actual divisibility.
The multiplier is regular modulo the parameter; separatedness of the quotient
is a consequence, not an input. -/
theorem dvd_of_adic_approximations (r ξ : R) (hr : r ≠ 0)
    (hξ : ∀ a : R, r ∣ ξ * a → r ∣ a)
    [IsAdicComplete (Ideal.span {r}) R] (x : R)
    (hx : ∀ n : ℕ, ∃ a : R, r ^ n ∣ x - ξ * a) : ξ ∣ x := by
  let I : Ideal R := Ideal.span {r}
  choose a ha using hx
  have hc : ∀ {m n : ℕ}, m ≤ n →
      a m ≡ a n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    apply (adic_dvd_mul_cancel r ξ hr hξ m _).mp
    have hn : r ^ m ∣ x - ξ * a n := (pow_dvd_pow r hmn).trans (ha n)
    convert dvd_sub hn (ha m) using 1
    ring
  obtain ⟨b, hb⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete I R) hc
  refine ⟨b, ?_⟩
  apply sub_eq_zero.mp
  apply IsHausdorff.haus' (I := I)
  intro n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  have hab : r ^ n ∣ a n - b := by
    simpa only [I, SModEq.sub_mem, smul_eq_mul, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] using hb n
  convert dvd_add (ha n) (hab.mul_left ξ) using 1
  ring

/-- In the parameter-adic topology, a regular principal ideal is closed. -/
theorem isClosed_span_of_adic_regular (r ξ : R) (hr : r ≠ 0)
    (hξ : ∀ a : R, r ∣ ξ * a → r ∣ a)
    [IsAdicComplete (Ideal.span {r}) R] [TopologicalSpace R]
    (hR : IsAdic (Ideal.span {r})) : IsClosed (Ideal.span {ξ} : Set R) := by
  rw [← closure_subset_iff_isClosed]
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  apply dvd_of_adic_approximations r ξ hr hξ x
  intro n
  have hn := (hR.hasBasis_nhds x).mem_of_mem (i := n) trivial
  obtain ⟨y, hy, hyξ⟩ := mem_closure_iff_nhds.mp hx _ hn
  obtain ⟨z, hz, rfl⟩ := hy
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hyξ
  refine ⟨a, ?_⟩
  have hz' : r ^ n ∣ z := by
    simpa only [Ideal.span_singleton_pow, SetLike.mem_coe,
      Ideal.mem_span_singleton] using hz
  convert hz'.neg_right using 1
  rw [← ha]
  ring

end PadicHodgeTheory
