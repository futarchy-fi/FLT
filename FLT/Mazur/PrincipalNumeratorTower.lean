/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalNumeratorTransition

/-!
# Coherent rescaled numerators through infinitely many orders

Individual numerator existence and principal-localization equality detection
construct a single monotone denominator sequence. Every transition is exact,
with the explicitly recorded change in exponent. A bound on that sequence
is a separate assertion and is not a consequence of this construction.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PrincipalNumeratorTower
variable {R S : ℕ → Type*} [∀ k, CommRing (R k)] [∀ k, CommRing (S k)]

/-- Recursively choose ideal-valued numerators with exact rescaled transitions. -/
theorem exists_rescaled_tower
    (f : ∀ k, R k →+* S k) (ρ : ∀ k, R (k + 1) →+* R k)
    (σ : ∀ k, S (k + 1) →+* S k) (hsq : ∀ k z, f k (ρ k z) = σ k (f (k + 1) z))
    (r : ∀ k, R k) (hr : ∀ k, ρ k (r (k + 1)) = r k)
    (x : ∀ k, S k) (hx : ∀ k, σ k (x (k + 1)) = x k) (I : ∀ k, Ideal (R k))
    (hdetect : ∀ k a b, f k a = f k b → ∃ d : ℕ, r k ^ d * a = r k ^ d * b)
    (hex : ∀ k, ∃ (m : ℕ) (z : R k), z ∈ I k ∧ f k z = f k (r k) ^ m * x k) :
    ∃ (N : ℕ → ℕ) (w : ∀ k, R k), Monotone N ∧
      (∀ k, w k ∈ I k) ∧ (∀ k, f k (w k) = f k (r k) ^ N k * x k) ∧
      ∀ k, ρ k (w (k + 1)) = r k ^ (N (k + 1) - N k) * w k := by
  classical
  let T (k : ℕ) := Σ m : ℕ, {z : R k // z ∈ I k ∧ f k z = f k (r k) ^ m * x k}
  have initial : Nonempty (T 0) := by
    obtain ⟨m, z, hz, he⟩ := hex 0
    exact ⟨⟨m, z, hz, he⟩⟩
  have next (k : ℕ) (t : T k) : ∃ u : T (k + 1), t.1 ≤ u.1 ∧
      ρ k u.2.val = r k ^ (u.1 - t.1) * t.2.val := by
    obtain ⟨m, z, hm, hz, he, ht⟩ :=
      PrincipalNumeratorTransition.exists_matching_numerator (f k) (f (k + 1))
        (ρ k) (σ k) (hsq k) (r k) (r (k + 1)) (hr k) (x k) (x (k + 1)) (hx k)
        (I (k + 1)) (hdetect k) (hex (k + 1)) t.1 t.2.val t.2.property.2
    exact ⟨⟨m, z, hz, he⟩, hm, ht⟩
  let t : ∀ k, T k := Nat.rec (Classical.choice initial) (fun k s ↦ (next k s).choose)
  refine ⟨fun k ↦ (t k).1, fun k ↦ (t k).2.val, ?_, ?_, ?_, ?_⟩
  · exact monotone_nat_of_le_succ (fun k ↦ (next k (t k)).choose_spec.1)
  · exact fun k ↦ (t k).2.property.1
  · exact fun k ↦ (t k).2.property.2
  · exact fun k ↦ (next k (t k)).choose_spec.2

/-- A proved denominator bound turns rescaled transitions into ordinary transitions. -/
theorem normalize_bounded_tower
    (f : ∀ k, R k →+* S k) (ρ : ∀ k, R (k + 1) →+* R k)
    (r : ∀ k, R k) (hr : ∀ k, ρ k (r (k + 1)) = r k)
    (x : ∀ k, S k) (I : ∀ k, Ideal (R k))
    (N : ℕ → ℕ) (hN : Monotone N) (w : ∀ k, R k)
    (hw : ∀ k, w k ∈ I k) (he : ∀ k, f k (w k) = f k (r k) ^ N k * x k)
    (ht : ∀ k, ρ k (w (k + 1)) = r k ^ (N (k + 1) - N k) * w k)
    (B : ℕ) (hB : ∀ k, N k ≤ B) :
    ∃ z : ∀ k, R k, (∀ k, z k ∈ I k) ∧
      (∀ k, f k (z k) = f k (r k) ^ B * x k) ∧
      ∀ k, ρ k (z (k + 1)) = z k := by
  refine ⟨fun k ↦ r k ^ (B - N k) * w k, fun k ↦ (I k).mul_mem_left _ (hw k),
    fun k ↦ PrincipalNumeratorTransition.promote (f k) (r k) (w k) (x k) (hB k) (he k),
    fun k ↦ ?_⟩
  rw [map_mul, map_pow, hr, ht, ← mul_assoc, ← pow_add]
  have hm : N k ≤ N (k + 1) := hN (Nat.le_succ k)
  have hb := hB (k + 1)
  congr 2
  omega

end FLT.Mazur.PrincipalNumeratorTower
