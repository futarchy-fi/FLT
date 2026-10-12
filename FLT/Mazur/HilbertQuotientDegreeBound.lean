/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertQuotientDegreeFiltration

/-!
# Uniform bounded-degree representatives of finite quotient algebras

A quotient of dimension `d` is generated as a vector space by polynomials of
total degree at most `d`. The bound is uniform in the ideal and the field,
including finite fields. No particular basis is required to work at two points.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart

variable (K I : Type*) [Field K] (J : Ideal (MvPolynomial I K))
variable [Module.Finite K (MvPolynomial I K ⧸ J)]

/-- Every `d`-dimensional quotient is spanned by its degree-at-most-`d` piece. -/
theorem quotientDegreePiece_eq_top (d : ℕ)
    (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) :
    quotientDegreePiece K I J d = ⊤ := by
  by_contra hne
  have hproper (n : ℕ) (hn : n ≤ d) : quotientDegreePiece K I J n ≠ ⊤ := by
    intro h
    apply hne
    exact top_unique (h ▸ quotientDegreePiece_mono K I J hn)
  have hrank (n : ℕ) (hn : n ≤ d) : n ≤ Module.finrank K (quotientDegreePiece K I J n) := by
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hn' : n ≤ d := (Nat.le_succ n).trans hn
      have hlt : Module.finrank K (quotientDegreePiece K I J n) <
          Module.finrank K (quotientDegreePiece K I J (n + 1)) := by
        by_contra h
        have he := Submodule.eq_of_le_of_finrank_le
          (quotientDegreePiece_mono K I J (Nat.le_succ n)) (Nat.le_of_not_gt h)
        exact hproper n hn' (quotientDegreePiece_eq_top_of_stable K I J n he)
      exact (Nat.succ_le_succ (ih hn')).trans hlt
  apply hne
  apply Submodule.eq_top_of_finrank_eq
  exact le_antisymm (Submodule.finrank_le _) (hd ▸ hrank d le_rfl)

/-- Every class has an actual representative whose total degree is bounded by the fiber rank. -/
theorem exists_quotient_representative_degree_le (d : ℕ)
    (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) (x : MvPolynomial I K ⧸ J) :
    ∃ p : MvPolynomial I K, p.totalDegree ≤ d ∧ Ideal.Quotient.mk J p = x := by
  apply (mem_quotientDegreePiece_iff K I J d x).mp
  rw [quotientDegreePiece_eq_top K I J d hd]
  trivial

/-- Restricting the actual quotient map to the uniform finite degree piece is surjective. -/
theorem quotient_restrictTotalDegree_surjective (d : ℕ)
    (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) :
    Function.Surjective (fun p : MvPolynomial.restrictTotalDegree I K d ↦
      Ideal.Quotient.mk J p.val) := by
  intro x
  obtain ⟨p, hp, hx⟩ := exists_quotient_representative_degree_le K I J d hd x
  exact ⟨⟨p, (MvPolynomial.mem_restrictTotalDegree I d p).mpr hp⟩, hx⟩

end FLT.Mazur.HilbertChart
