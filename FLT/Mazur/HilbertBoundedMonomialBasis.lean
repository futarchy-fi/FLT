/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertQuotientDegreeBound

/-!
# A uniform finite set of monomials for Hilbert fibers

For a finite ambient variable set, the monomials of degree at most `d` form
one finite indexing set independent of the field and the quotient ideal.
Every rank-`d` fiber has a basis selected from this set; the selection may
vary between fibers, as it must over small finite fields.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.HilbertChart

/-- Ambient monomials with the uniform total-degree bound. -/
def BoundedHilbertMonomials (I : Type*) (d : ℕ) :=
  {m : I →₀ ℕ // m.sum (fun _ e ↦ e) ≤ d}

/-- The coordinate bound follows from the total-degree bound. -/
theorem boundedHilbertMonomial_le {I : Type*} {d : ℕ}
    (m : BoundedHilbertMonomials I d) (i : I) : m.val i ≤ d := by
  classical
  by_cases h : m.val i = 0
  · exact h ▸ Nat.zero_le d
  · exact (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finsupp.mem_support_iff.mpr h)).trans m.property

instance {I : Type*} [Finite I] (d : ℕ) : Finite (BoundedHilbertMonomials I d) := by
  let g : BoundedHilbertMonomials I d → (I → Fin (d + 1)) :=
    fun m i ↦ ⟨m.val i, Nat.lt_succ_of_le (boundedHilbertMonomial_le m i)⟩
  apply Finite.of_injective g
  intro m n h
  apply Subtype.ext
  ext i
  exact congrArg (fun v : I → Fin (d + 1) ↦ (v i).val) h

variable (K I : Type*) [Field K] (J : Ideal (MvPolynomial I K))

/-- The degree piece is exactly the span of the uniformly bounded ambient monomials. -/
theorem quotientDegreePiece_eq_boundedMonomial_span (d : ℕ) :
    quotientDegreePiece K I J d = Submodule.span K
      (Set.range (fun m : BoundedHilbertMonomials I d ↦
        Ideal.Quotient.mk J (MvPolynomial.monomial m.val (1 : K)))) := by
  rw [quotientDegreePiece, MvPolynomial.restrictTotalDegree,
    MvPolynomial.restrictSupport_eq_span, Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨⟨m, hm⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    exact ⟨_, ⟨m.val, m.property, rfl⟩, rfl⟩

variable [Module.Finite K (MvPolynomial I K ⧸ J)]

/-- The same bounded monomial family spans every quotient of dimension `d`. -/
theorem boundedHilbertMonomials_span (d : ℕ)
    (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) :
    Submodule.span K (Set.range (fun m : BoundedHilbertMonomials I d ↦
      Ideal.Quotient.mk J (MvPolynomial.monomial m.val (1 : K)))) = ⊤ := by
  rw [← quotientDegreePiece_eq_boundedMonomial_span, quotientDegreePiece_eq_top K I J d hd]

/-- Each fiber chooses a basis from the uniform bounded monomials, without sharing that choice. -/
theorem exists_quotient_boundedMonomial_basis (d : ℕ)
    (hd : Module.finrank K (MvPolynomial I K ⧸ J) = d) :
    ∃ m : Fin d → BoundedHilbertMonomials I d,
      ∃ b : Module.Basis (Fin d) K (MvPolynomial I K ⧸ J),
        ∀ i, b i = Ideal.Quotient.mk J (MvPolynomial.monomial (m i).val (1 : K)) :=
  exists_basis_from_spanning_family _ (boundedHilbertMonomials_span K I J d hd) d hd

end FLT.Mazur.HilbertChart
