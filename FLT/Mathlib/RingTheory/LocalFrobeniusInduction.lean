/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.RingTheory.FrobeniusImage
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Induction through local Frobenius images

Passing to the Frobenius image decreases the augmentation height by one.
For a finite local augmented algebra larger than its coefficient field, it
also strictly decreases dimension. Either measure can therefore be used to
organize the higher-height structure theorem.
-/

@[expose] public noncomputable section

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

/-- Passing to the Frobenius image lowers the augmentation height by one. -/
theorem pow_eq_zero_on_ker_frobeniusImage (ε : A →ₐ[k] k) (n : ℕ)
    (h : ∀ a ∈ RingHom.ker ε, a ^ p ^ (n + 1) = 0)
    (c : Algebra.frobeniusImage k A p 1)
    (hc : (ε.comp (Algebra.frobeniusImage k A p 1).val) c = 0) :
    c ^ p ^ n = 0 := by
  obtain ⟨a, ha⟩ := c.property
  have hac : a ^ p = (c : A) := by simpa only [iterateFrobenius_def, pow_one] using ha
  have hε : ε a = 0 := by
    have hpow : (ε a) ^ p = 0 := by rw [← map_pow, hac]; exact hc
    exact (pow_eq_zero_iff (Fact.out : p.Prime).ne_zero).mp hpow
  apply Subtype.ext
  change (c : A) ^ p ^ n = 0
  rw [← hac, ← pow_mul, ← pow_succ']
  exact h a hε

variable [Module.Finite k A] [IsLocalRing A]

/-- The Frobenius image is proper unless the original algebra consists of scalars. -/
theorem frobeniusImage_ne_top (ε : A →ₐ[k] k) (hA : (⊥ : Subalgebra k A) ≠ ⊤) :
    Algebra.frobeniusImage k A p 1 ≠ ⊤ := by
  intro htop
  have hsurj : Function.Surjective (frobenius A p) := by
    intro a
    have ha : a ∈ Algebra.frobeniusImage k A p 1 := by rw [htop]; trivial
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, by simpa only [iterateFrobenius_one] using hb⟩
  obtain ⟨n, hn⟩ := ε.exists_frobeniusImage_eq_bot p
  apply hA
  apply top_unique
  intro a _
  obtain ⟨b, hb⟩ := hsurj.iterate n a
  have ha : a ∈ Algebra.frobeniusImage k A p n := by
    refine ⟨b, ?_⟩
    simpa only [coe_iterateFrobenius] using hb
  rwa [hn] at ha

/-- Frobenius strictly decreases the dimension of a nontrivial finite local
augmented algebra over a perfect field. -/
theorem finrank_frobeniusImage_lt (ε : A →ₐ[k] k) (hA : (⊥ : Subalgebra k A) ≠ ⊤) :
    Module.finrank k (Algebra.frobeniusImage k A p 1) < Module.finrank k A := by
  apply Submodule.finrank_lt (s := (Algebra.frobeniusImage k A p 1).toSubmodule)
  intro h
  apply ε.frobeniusImage_ne_top p hA
  exact Subalgebra.toSubmodule_injective h

end AlgHom
