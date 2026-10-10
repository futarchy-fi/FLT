/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginParameterOrder

/-!
# Finite expansions at the original elliptic origin

Repeated division by the actual regular parameter supplies an expansion of
every function to every finite order. No field, reduction, completion, or
choice of a new curve is used.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-- Evaluate finite parameter coefficients by the Horner rule in the actual origin ring. -/
def originJet (c : ℕ → R) : ℕ → OriginNeighborhood W
  | 0 => 0
  | n + 1 => algebraMap R _ (c 0) + originCoordinate W 0 * originJet (c ∘ Nat.succ) n

/-- Every actual function has a finite expansion with a remainder divisible by the next power. -/
theorem originJet_exists (a : OriginNeighborhood W) (n : ℕ) :
    ∃ (c : ℕ → R) (b : OriginNeighborhood W),
      a = originJet W c n + originCoordinate W 0 ^ n * b := by
  induction n generalizing a with
  | zero => exact ⟨fun _ ↦ 0, a, by simp [originJet]⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := originParameter_division W a
    obtain ⟨c, d, hd⟩ := ih b
    let c' : ℕ → R := fun k ↦ match k with
      | 0 => originEvaluation W a
      | k + 1 => c k
    refine ⟨c', d, ?_⟩
    change a = algebraMap R _ (originEvaluation W a) +
      originCoordinate W 0 * originJet W c n + originCoordinate W 0 ^ (n + 1) * d
    calc
      a = algebraMap R _ (originEvaluation W a) + originCoordinate W 0 * b := hb
      _ = _ := by rw [hd, pow_succ]; ring

/-- Evaluation at the original zero section recovers the constant coefficient of a finite jet. -/
theorem originJet_evaluation (c : ℕ → R) (n : ℕ) :
    originEvaluation W (originJet W c (n + 1)) = c 0 := by
  simp [originJet]

/-- A finite expansion vanishes to its full length only when every retained coefficient vanishes. -/
theorem originJet_mem_power_iff (c : ℕ → R) (n : ℕ) :
    originJet W c n ∈ Ideal.span {originCoordinate W 0 ^ n} ↔ ∀ i < n, c i = 0 := by
  induction n generalizing c with
  | zero => simp [originJet]
  | succ n ih =>
    constructor
    · intro h
      have h0 : c 0 = 0 := by
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h
        have he := congrArg (originEvaluation W) hb
        simpa [originJet, pow_succ] using he
      have hn : originJet W (c ∘ Nat.succ) n ∈ Ideal.span {originCoordinate W 0 ^ n} := by
        obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp h
        apply Ideal.mem_span_singleton.mpr
        refine ⟨b, ?_⟩
        apply (originCoordinate_x_regular W).left
        simpa [originJet, h0, pow_succ, mul_comm, mul_left_comm, mul_assoc] using hb
      intro i hi
      cases i with
      | zero => exact h0
      | succ i => exact (ih (c ∘ Nat.succ)).mp hn i (Nat.lt_of_succ_lt_succ hi)
    · intro hc
      have h0 := hc 0 (Nat.zero_lt_succ n)
      have hn : originJet W (c ∘ Nat.succ) n ∈ Ideal.span {originCoordinate W 0 ^ n} :=
        (ih (c ∘ Nat.succ)).mpr (fun i hi ↦ hc (i + 1) (Nat.succ_lt_succ hi))
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hn
      apply Ideal.mem_span_singleton.mpr
      refine ⟨b, ?_⟩
      simp [originJet, h0, hb, pow_succ, mul_comm, mul_left_comm]

end FLT.Mazur.WeierstrassIntegralChart
