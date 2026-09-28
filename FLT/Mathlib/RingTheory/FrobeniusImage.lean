/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Frobenius images over a perfect field

The image of an iterated Frobenius is a subalgebra over a perfect field.
For a finite local augmented algebra, sufficiently high iterates have image
exactly the coefficient field. These are the algebraic descent ingredients
for induction on the height of a finite local group scheme.
-/

@[expose] public noncomputable section

namespace Algebra

variable (k A : Type*) [Field k] [CommRing A] [Algebra k A]
variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p] [PerfectRing k p]

/-- The subalgebra of `p ^ n`-th powers over a perfect coefficient field. -/
def frobeniusImage (n : ℕ) : Subalgebra k A where
  __ := (iterateFrobenius A p n).range
  algebraMap_mem' c := by
    obtain ⟨b, hb⟩ := (bijective_iterateFrobenius k p n).surjective c
    exact ⟨algebraMap k A b, by
      change (algebraMap k A b) ^ p ^ n = algebraMap k A c
      rw [← map_pow]
      exact congrArg (algebraMap k A) hb⟩

/-- Membership in the Frobenius image is existence of a power root. -/
theorem mem_frobeniusImage_iff (n : ℕ) (a : A) :
    a ∈ frobeniusImage k A p n ↔ ∃ b : A, b ^ p ^ n = a := Iff.rfl

/-- The zeroth Frobenius image is the whole algebra. -/
@[simp] theorem frobeniusImage_zero : frobeniusImage k A p 0 = ⊤ := by
  ext a
  simp [mem_frobeniusImage_iff]

/-- Successive Frobenius images form a descending chain. -/
theorem frobeniusImage_succ_le (n : ℕ) :
    frobeniusImage k A p (n + 1) ≤ frobeniusImage k A p n := by
  rintro a ⟨b, rfl⟩
  exact ⟨b ^ p, by simp only [iterateFrobenius_def, ← pow_mul, pow_succ']⟩

/-- A Frobenius image of a finite local algebra is again local. -/
theorem isLocalRing_frobeniusImage [Module.Finite k A] [IsLocalRing A] (n : ℕ) :
    IsLocalRing (frobeniusImage k A p n) := by
  let C := frobeniusImage k A p n
  let : Module.Finite C A := Module.Finite.of_restrictScalars_finite k C A
  exact RingHom.domain_isLocalRing (algebraMap C A)

end Algebra

namespace AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A]
  [Module.Finite k A] [IsLocalRing A]

/-- The augmentation ideal of a finite local algebra is nilpotent. -/
theorem isNilpotent_ker_of_finite_local (ε : A →ₐ[k] k) :
    IsNilpotent (RingHom.ker ε) := by
  let : IsArtinianRing A := IsArtinianRing.of_finite k A
  have hle : RingHom.ker ε ≤ Ideal.jacobson (⊥ : Ideal A) := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top ε)
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  exact ⟨n, le_bot_iff.mp ((pow_le_pow_left' hle n).trans hn.le)⟩

variable (p : ℕ) [Fact p.Prime] [CharP k p] [CharP A p]

omit [CharP k p] [CharP A p] in
/-- A uniform Frobenius iterate kills the augmentation ideal of a finite local algebra. -/
theorem exists_pow_eq_zero_on_ker (ε : A →ₐ[k] k) :
    ∃ n : ℕ, ∀ a ∈ RingHom.ker ε, a ^ p ^ n = 0 := by
  obtain ⟨N, hN⟩ := ε.isNilpotent_ker_of_finite_local
  refine ⟨N, fun a ha ↦ ?_⟩
  have haN : a ^ N = 0 := by
    have hm := Ideal.pow_mem_pow ha N
    simpa only [hN, Ideal.zero_eq_bot, Ideal.mem_bot] using hm
  exact pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le haN

omit [CharP k p] in
/-- A sufficiently high Frobenius iterate is determined by the augmentation. -/
theorem exists_iterateFrobenius_eq_augmentation (ε : A →ₐ[k] k) :
    ∃ n : ℕ, ∀ a : A, a ^ p ^ n = algebraMap k A ((ε a) ^ p ^ n) := by
  obtain ⟨n, hn⟩ := ε.exists_pow_eq_zero_on_ker p
  refine ⟨n, fun a ↦ ?_⟩
  have h := hn (a - algebraMap k A (ε a)) (by simp [RingHom.mem_ker])
  rwa [sub_pow_expChar_pow, ← map_pow, sub_eq_zero] at h

/-- Over a perfect field, the Frobenius images of a finite local augmented algebra
reach the coefficient field after finitely many steps. -/
theorem exists_frobeniusImage_eq_bot [PerfectRing k p] (ε : A →ₐ[k] k) :
    ∃ n : ℕ, Algebra.frobeniusImage k A p n = ⊥ := by
  obtain ⟨n, hn⟩ := ε.exists_iterateFrobenius_eq_augmentation p
  refine ⟨n, le_bot_iff.mp ?_⟩
  rintro a ⟨b, rfl⟩
  rw [iterateFrobenius_def, hn]
  exact (⊥ : Subalgebra k A).algebraMap_mem _

end AlgHom
