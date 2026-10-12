/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertTruncatedIdealGeneration

/-!
# Full Hilbert ideals are detected by bounded relations

For quotient algebras of dimension at most `d`, the subspace of relations in
degree at most `d + 1` determines the entire ideal, including nilpotents. This
is the injectivity step toward finite-dimensional Hilbert parameters. It does
not yet construct a Grassmannian immersion or an ample line bundle.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart

variable (S I : Type*) [CommRing S] (J K : Ideal (MvPolynomial I S)) (d : ℕ)

/-- A bounded-degree relation test detects inclusion of the entire source ideal. -/
theorem ideal_le_of_bounded_relations
    (hrep : ∀ x : MvPolynomial I S ⧸ J,
      ∃ p : MvPolynomial I S, p.totalDegree ≤ d ∧ Ideal.Quotient.mk J p = x)
    (h : ∀ p : MvPolynomial I S, p.totalDegree ≤ d + 1 → p ∈ J → p ∈ K) : J ≤ K := by
  rw [← truncatedRelationIdeal_eq S I J d hrep]
  exact Ideal.span_le.mpr (fun p hp ↦ h p hp.2 hp.1)

/-- Over any coefficient ring with bounded representatives, truncation detects ideal equality. -/
theorem ideal_eq_of_bounded_relations
    (hJ : ∀ x : MvPolynomial I S ⧸ J,
      ∃ p : MvPolynomial I S, p.totalDegree ≤ d ∧ Ideal.Quotient.mk J p = x)
    (hK : ∀ x : MvPolynomial I S ⧸ K,
      ∃ p : MvPolynomial I S, p.totalDegree ≤ d ∧ Ideal.Quotient.mk K p = x)
    (h : ∀ p : MvPolynomial I S, p.totalDegree ≤ d + 1 → (p ∈ J ↔ p ∈ K)) : J = K :=
  le_antisymm (ideal_le_of_bounded_relations S I J K d hJ (fun p hp ↦ (h p hp).mp))
    (ideal_le_of_bounded_relations S I K J d hK (fun p hp ↦ (h p hp).mpr))

/-- The actual submodule of polynomial relations in a fixed degree range. -/
def truncatedIdealSubmodule (n : ℕ) : Submodule S (MvPolynomial I S) :=
  J.restrictScalars S ⊓ MvPolynomial.restrictTotalDegree I S n

/-- Membership retains both the original ideal and the degree condition. -/
theorem mem_truncatedIdealSubmodule (n : ℕ) (p : MvPolynomial I S) :
    p ∈ truncatedIdealSubmodule S I J n ↔ p ∈ J ∧ p.totalDegree ≤ n := by
  simp only [truncatedIdealSubmodule, Submodule.mem_inf,
    Submodule.restrictScalars_mem, MvPolynomial.mem_restrictTotalDegree]

variable (F : Type*) [Field F] (A B : Ideal (MvPolynomial I F))
variable [Module.Finite F (MvPolynomial I F ⧸ A)]
  [Module.Finite F (MvPolynomial I F ⧸ B)]

/-- A rank upper bound also supplies bounded representatives, including the zero quotient. -/
theorem exists_quotient_representative_of_finrank_le
    (hA : Module.finrank F (MvPolynomial I F ⧸ A) ≤ d) (x : MvPolynomial I F ⧸ A) :
    ∃ p : MvPolynomial I F, p.totalDegree ≤ d ∧ Ideal.Quotient.mk A p = x := by
  obtain ⟨p, hp, hx⟩ := exists_quotient_representative_degree_le F I A _ rfl x
  exact ⟨p, hp.trans hA, hx⟩

/-- Equal bounded relation subspaces imply equal full finite quotient ideals. -/
theorem finiteQuotient_ideal_eq_iff_truncated
    (hA : Module.finrank F (MvPolynomial I F ⧸ A) ≤ d)
    (hB : Module.finrank F (MvPolynomial I F ⧸ B) ≤ d) :
    A = B ↔ truncatedIdealSubmodule F I A (d + 1) =
      truncatedIdealSubmodule F I B (d + 1) := by
  constructor
  · rintro rfl
    rfl
  · intro h
    apply ideal_eq_of_bounded_relations F I A B d
      (exists_quotient_representative_of_finrank_le I d F A hA)
      (exists_quotient_representative_of_finrank_le I d F B hB)
    intro p hp
    have he := SetLike.ext_iff.mp h p
    simpa only [mem_truncatedIdealSubmodule, hp, and_true] using he

end FLT.Mazur.HilbertChart
