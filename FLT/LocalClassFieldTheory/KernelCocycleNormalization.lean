/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.Tactic.Abel

/-!
# Removing a restricted two-boundary

Extend the bounding cochain by zero off the subgroup and subtract its
differential. The result vanishes on the subgroup square.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open groupCohomology

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]

/-- Subtract the differential of a one-cochain. -/
def correctTwoCocycle (c : G × G → M) (b : G → M) : G × G → M :=
  fun p => c p - (p.1 • b p.2 - b (p.1 * p.2) + b p.1)

/-- Subtracting a differential preserves the two-cocycle equation. -/
theorem correctTwoCocycle_isCocycle (c : G × G → M) (hc : IsCocycle₂ c) (b : G → M) :
    IsCocycle₂ (correctTwoCocycle c b) := by
  intro g h j
  simp only [correctTwoCocycle, smul_sub, smul_add, ← mul_smul, mul_assoc]
  have he := hc g h j
  calc
    _ = (c (g * h, j) + c (g, h)) -
      ((g * h) • b j - b (g * (h * j)) + g • b h + b g) := by abel
    _ = _ := by rw [he]; abel

/-- Successive corrections add their bounding cochains. -/
theorem correctTwoCocycle_add (c : G × G → M) (a b : G → M) :
    correctTwoCocycle (correctTwoCocycle c a) b = correctTwoCocycle c (a + b) := by
  funext p
  simp only [correctTwoCocycle, Pi.add_apply, smul_add]
  abel

/-- A cochain whose restriction is a boundary has a representative vanishing there. -/
theorem exists_kernel_zero_twoCocycle (N : Subgroup G) (c : G × G → M)
    (hc : IsCocycle₂ c) (b : N → M)
    (hb : ∀ n m : N, c (n, m) = n • b m - b (n * m) + b n) :
    ∃ a : G → M, IsCocycle₂ (correctTwoCocycle c a) ∧
      ∀ n m : N, correctTwoCocycle c a (n, m) = 0 := by
  classical
  let a : G → M := fun g => if h : g ∈ N then b ⟨g, h⟩ else 0
  have ha (n : N) : a n = b n := dite_eq_left n.property
  refine ⟨a, correctTwoCocycle_isCocycle c hc a, fun n m => ?_⟩
  change c (n, m) - ((n : G) • a m - a ((n * m : N) : G) + a n) = 0
  rw [ha n, ha m, ha (n * m), hb]
  exact sub_self _

/-- Vanishing on a subgroup square normalizes the first argument. -/
theorem kernel_zero_twoCocycle_one_left (N : Subgroup G) (c : G × G → M)
    (hc : IsCocycle₂ c) (hN : ∀ n m : N, c (n, m) = 0) (g : G) : c (1, g) = 0 := by
  rw [map_one_fst_of_isCocycle₂ hc]
  exact hN 1 1

/-- Vanishing on a subgroup square normalizes the second argument. -/
theorem kernel_zero_twoCocycle_one_right (N : Subgroup G) (c : G × G → M)
    (hc : IsCocycle₂ c) (hN : ∀ n m : N, c (n, m) = 0) (g : G) : c (g, 1) = 0 := by
  have h0 : c (1, 1) = 0 := hN 1 1
  rw [map_one_snd_of_isCocycle₂ hc, h0, smul_zero]

end LocalClassFieldTheory
