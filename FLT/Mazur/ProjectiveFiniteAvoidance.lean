/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveFiniteSeparation

/-!
# Positive homogeneous prime avoidance for finite projective sets

Induct on a finite set, removing a minimal prime. A separator vanishes at
all remaining primes; adding suitable powers keeps a common homogeneous
degree and avoids cancellation at every prescribed point.
-/

@[expose] public noncomputable section

open AlgebraicGeometry MvPolynomial

universe u v

namespace FLT.Mazur.ProjectiveSpace

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {ι : Type v}

/-- A finite projective set is contained in one positive homogeneous basic open. -/
theorem exists_homogeneous_avoiding_finset (T : Finset (space R ι)) :
    ∃ (n : ℕ) (f : MvPolynomial ι R), 0 < n ∧ f.IsHomogeneous n ∧
      ∀ p ∈ T, f ∉ p.asHomogeneousIdeal := by
  classical
  induction T using Finset.strongInductionOn
  rename_i T ih
  rcases T.eq_empty_or_nonempty with rfl | hT
  · exact ⟨1, 0, by decide, isHomogeneous_zero ι R 1, by simp⟩
  obtain ⟨p, hp, hmin⟩ := T.exists_minimalFor
    (fun p ↦ p.asHomogeneousIdeal.toIdeal) hT
  obtain ⟨n, f, hn, hf, hfT⟩ := ih (T.erase p) (Finset.erase_ssubset hp)
  by_cases hfp : f ∈ p.asHomogeneousIdeal
  · have hsep : ∀ q ∈ T.erase p,
        ¬ q.asHomogeneousIdeal.toIdeal ≤ p.asHomogeneousIdeal.toIdeal := by
      intro q hq hqp
      have hpq := hmin (Finset.mem_of_mem_erase hq) hqp
      have he : q = p := by
        apply ProjectiveSpectrum.ext
        apply HomogeneousIdeal.ext
        exact le_antisymm hqp hpq
      exact (Finset.ne_of_mem_erase hq) he
    obtain ⟨m, g, hm, hg, hgp, hgT⟩ := exists_homogeneous_finite_separator p (T.erase p) hsep
    refine ⟨n * m, f ^ m + g ^ n, Nat.mul_pos hn hm,
      (hf.pow m).add (by simpa only [Nat.mul_comm] using hg.pow n), ?_⟩
    intro q hq hsum
    by_cases hqp : q = p
    · subst q
      have hpow := p.asHomogeneousIdeal.toIdeal.pow_mem_of_mem hfp m hm
      exact hgp (p.isPrime.mem_of_pow_mem n
        ((p.asHomogeneousIdeal.toIdeal.add_mem_iff_right hpow).mp hsum))
    · have hqT := Finset.mem_erase.mpr ⟨hqp, hq⟩
      have hpow := q.asHomogeneousIdeal.toIdeal.pow_mem_of_mem (hgT q hqT) n hn
      exact hfT q hqT (q.isPrime.mem_of_pow_mem m
        ((q.asHomogeneousIdeal.toIdeal.add_mem_iff_left hpow).mp hsum))
  · refine ⟨n, f, hn, hf, fun q hq ↦ ?_⟩
    by_cases hqp : q = p
    · simpa only [hqp] using hfp
    · exact hfT q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

/-- Arbitrary finite sets, including the empty set, have a homogeneous avoiding polynomial. -/
theorem exists_homogeneous_avoiding_finite (T : Set (space R ι)) (hT : T.Finite) :
    ∃ (n : ℕ) (f : MvPolynomial ι R), 0 < n ∧ f.IsHomogeneous n ∧
      ∀ p ∈ T, f ∉ p.asHomogeneousIdeal := by
  classical
  simpa only [Set.Finite.mem_toFinset] using exists_homogeneous_avoiding_finset hT.toFinset

end FLT.Mazur.ProjectiveSpace
