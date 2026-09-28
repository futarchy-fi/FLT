/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic

/-!
# Actions filtered by trivial modules killed by a prime

A finite filtration with trivial, prime-torsion graded pieces makes the full
action image a prime group. It does not make the action itself trivial.
The hypotheses concern additive point groups; constructing this filtration from
a filtration of finite-flat group schemes is a separate geometric step.
-/

@[expose] public section

namespace ThreeAdicPlan

/-- An ascending finite filtration of an additive group, with every graded piece
killed by `p` and carrying the trivial action of `G`. No splitting is required. -/
structure TrivialPrimeFiltration (p : ℕ) (G W : Type*) [Group G]
    [AddCommGroup W] [DistribMulAction G W] where
  /-- The number of steps in the filtration. -/
  length : ℕ
  /-- The additive subgroups in the filtration. -/
  step : ℕ → AddSubgroup W
  /-- The filtration starts at zero. -/
  stepZero : step 0 = ⊥
  /-- The filtration exhausts the point group. -/
  stepLength : step length = ⊤
  /-- Each subgroup is contained in its successor. -/
  stepLe : ∀ i < length, step i ≤ step (i + 1)
  /-- Multiplication by `p` lowers the filtration by one step. -/
  nsmulMem : ∀ i < length, ∀ w ∈ step (i + 1), p • w ∈ step i
  /-- The displacement of every action element lowers the filtration by one step. -/
  smulSubMem : ∀ i < length, ∀ (g : G) (w : W), w ∈ step (i + 1) →
    g • w - w ∈ step i

/-- When an element fixes its displacement on a point, its powers add that displacement. -/
theorem pow_smul_eq_add_nsmul_sub {G W : Type*} [Group G]
    [AddCommGroup W] [DistribMulAction G W] (g : G) (w : W)
    (h : g • (g • w - w) = g • w - w) (n : ℕ) :
    g ^ n • w = w + n • (g • w - w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', mul_smul, ih, smul_add, smul_comm g n, h, add_nsmul, one_nsmul]
    abel

namespace TrivialPrimeFiltration

variable {p : ℕ} {G W : Type*} [Group G] [AddCommGroup W] [DistribMulAction G W]
  (F : TrivialPrimeFiltration p G W)

/-- The `i`th filtered subgroup is killed by `p^i`. -/
theorem pow_nsmul_eq_zero (i : ℕ) (hi : i ≤ F.length) (w : W) (hw : w ∈ F.step i) :
    (p ^ i) • w = 0 := by
  induction i generalizing w with
  | zero =>
    have hw0 : w = 0 := by simpa [F.stepZero] using hw
    simp [hw0]
  | succ i ih =>
    rw [pow_succ', mul_nsmul]
    exact ih (by omega) _ (F.nsmulMem i (by omega) w hw)

/-- At each step a single power of `p` annihilates the action of every group element. -/
theorem exists_pow_smul_eq (i : ℕ) (hi : i ≤ F.length) :
    ∃ k : ℕ, ∀ (g : G) (w : W), w ∈ F.step i → g ^ (p ^ k) • w = w := by
  induction i with
  | zero =>
    refine ⟨0, fun g w hw ↦ ?_⟩
    have hw0 : w = 0 := by simpa [F.stepZero] using hw
    simp [hw0]
  | succ i ih =>
    obtain ⟨k, hk⟩ := ih (by omega)
    refine ⟨k + i, fun g w hw ↦ ?_⟩
    have hd : g ^ (p ^ k) • w - w ∈ F.step i :=
      F.smulSubMem i (by omega) _ w hw
    have heq := pow_smul_eq_add_nsmul_sub (g ^ (p ^ k)) w (hk g _ hd) (p ^ i)
    rw [F.pow_nsmul_eq_zero i (by omega) _ hd, add_zero] at heq
    simpa only [pow_add, pow_mul] using heq

include F in
/-- The full permutation image of an action with trivial `p`-torsion graded pieces
is a `p`-group. This conclusion does not require the acting group to be finite. -/
theorem isPGroup_range : IsPGroup p (MulAction.toPermHom G W).range := by
  obtain ⟨k, hk⟩ := F.exists_pow_smul_eq F.length le_rfl
  intro a
  obtain ⟨g, hg⟩ := a.property
  refine ⟨k, ?_⟩
  apply Subtype.ext
  change a.val ^ (p ^ k) = 1
  rw [← hg, ← map_pow]
  apply Equiv.ext
  intro w
  exact hk g w (F.stepLength ▸ AddSubgroup.mem_top w)

end TrivialPrimeFiltration

end ThreeAdicPlan
