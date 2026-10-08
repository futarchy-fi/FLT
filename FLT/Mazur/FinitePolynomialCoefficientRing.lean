/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Adjoin.FG

/-!
# A common Noetherian ring for finitely many polynomials

Polynomials in different variable sets can share one finite coefficient ring.
This is the coefficient step for simultaneous, rather than successive,
closure of relation ideals in a finite diagram.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FinitePolynomialCoefficients

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
  {σ : ι → Type w} (p : ∀ i, MvPolynomial (σ i) R)

/-- Finitely many polynomials lift to one finitely generated coefficient subring. -/
theorem exists_coefficient_ring :
    ∃ S : Subring R, IsNoetherianRing S ∧
      ∀ i, ∃ q : MvPolynomial (σ i) S, MvPolynomial.map S.subtype q = p i := by
  classical
  let _ := Fintype.ofFinite ι
  let c : Finset R := Finset.univ.biUnion fun i ↦ (p i).coeffs
  let S := Subring.closure (c : Set R)
  refine ⟨S, is_noetherian_subring_closure _ c.finite_toSet, fun i ↦ ?_⟩
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro r hr
  have hc : r ∈ c := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hr⟩
  exact ⟨⟨r, Subring.subset_closure hc⟩, rfl⟩

/-- Coefficient extension from a subring is injective on polynomials. -/
theorem coefficient_map_injective (S : Subring R) (τ : Type w) :
    Function.Injective (MvPolynomial.map (σ := τ) S.subtype) :=
  MvPolynomial.map_injective S.subtype Subtype.val_injective

end FLT.Mazur.FinitePolynomialCoefficients
