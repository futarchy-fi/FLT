/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # Distinct polynomial variables form a regular sequence -/

@[expose] public section

namespace MvPolynomial

open RingTheory.Sequence

variable {R σ : Type*} [CommRing R]

/-- A variable outside a set of variables is regular modulo their ideal. -/
theorem isSMulRegular_quotient_span_X {s : Set σ} {i : σ} (hi : i ∉ s) :
    IsSMulRegular (MvPolynomial σ R ⧸ Ideal.span (X (R := R) '' s)) (X i : MvPolynomial σ R) := by
  classical
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem _ _).mpr
  intro f hf
  rw [smul_eq_mul, mem_ideal_span_X_image] at hf
  rw [mem_ideal_span_X_image]
  intro m hm
  have hm' : Finsupp.single i 1 + m ∈ (X i * f).support := by
    simpa only [mem_support_iff, coeff_X_mul] using mem_support_iff.mp hm
  obtain ⟨j, hj, he⟩ := hf _ hm'
  refine ⟨j, hj, ?_⟩
  have hji : i ≠ j := fun h ↦ hi (h.symm ▸ hj)
  simpa [Finsupp.single_apply, hji, Ne.symm hji] using he

/-- Any list of distinct variables is weakly regular over any commutative ring. -/
theorem isWeaklyRegular_X_list {is : List σ} (hi : is.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (is.map (X (R := R))) := by
  classical
  constructor
  intro n hn
  have hn' : n < is.length := by simpa using hn
  have hspan : Ideal.ofList ((is.map (X (R := R))).take n) =
      Ideal.span (X '' {j | j ∈ is.take n}) := by
    rw [← List.map_take]
    exact congrArg Ideal.span (Set.ext fun f ↦ List.mem_map)
  rw [hspan, Ideal.smul_eq_mul, Ideal.mul_top, List.getElem_map]
  apply isSMulRegular_quotient_span_X
  intro h
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp h
  have hj' : j < is.length := lt_of_lt_of_le hj (by simp)
  have he' : is[j] = is[n] := by simpa using he
  have hjn := hi.getElem_inj_iff.mp he'
  have : j < n := lt_of_lt_of_le hj (by simp)
  omega

/-- Distinct variables form a regular sequence when the coefficient ring is nonzero. -/
theorem isRegular_X_list [Nontrivial R] {is : List σ} (hi : is.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (is.map (X (R := R))) := by
  refine ⟨isWeaklyRegular_X_list hi, ?_⟩
  rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have hle : Ideal.ofList (is.map (X (R := R))) ≤ RingHom.ker constantCoeff := by
    apply Ideal.span_le.mpr
    intro f hf
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
    simp
  intro h
  have hmem := hle (h ▸ (show (1 : MvPolynomial σ R) ∈ (⊤ : Ideal _) from trivial))
  simp at hmem

end MvPolynomial
