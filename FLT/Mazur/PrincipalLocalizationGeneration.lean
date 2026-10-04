/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# Generation of a principal localization

Generators of the original algebra, together with the inverse of the chosen
denominator, suffice. Keeping the inverse as an explicit obligation prevents
an arbitrary source refinement from being mistaken for a surjective chart map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.PrincipalLocalizationGeneration

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
  [Algebra K R] [Algebra K S]

/-- A fraction is a numerator multiplied by a power of the chosen inverse. -/
lemma fraction_representation (s : R) (z : Localization.Away s) :
    ∃ (a : R) (n : ℕ), z = algebraMap R (Localization.Away s) a *
      IsLocalization.Away.invSelf s ^ n := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj s z
  refine ⟨a, n, ?_⟩
  calc
    z = z * (algebraMap R (Localization.Away s) s *
        IsLocalization.Away.invSelf s) ^ n := by rw [IsLocalization.Away.mul_invSelf]; simp
    _ = algebraMap R (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n := by
      rw [mul_pow, ← mul_assoc, ha]

/-- Algebra generators and the denominator inverse generate the entire localization. -/
lemma surjective_of_generators (s : R) (G : Set R) (hG : Algebra.adjoin K G = ⊤)
    (f : S →ₐ[K] Localization.Away s)
    (hg : ∀ g ∈ G, algebraMap R (Localization.Away s) g ∈ f.range)
    (hi : IsLocalization.Away.invSelf s ∈ f.range) : Function.Surjective f := by
  have hr : ∀ a : R, algebraMap R (Localization.Away s) a ∈ f.range := by
    have hh : Algebra.adjoin K G ≤
        f.range.comap (IsScalarTower.toAlgHom K R (Localization.Away s)) :=
      Algebra.adjoin_le hg
    rw [hG] at hh
    intro a
    exact hh (show a ∈ (⊤ : Subalgebra K R) from trivial)
  intro z
  obtain ⟨a, n, rfl⟩ := fraction_representation s z
  exact f.range.mul_mem (hr a) (f.range.pow_mem hi n)

end FLT.Mazur.PrincipalLocalizationGeneration
