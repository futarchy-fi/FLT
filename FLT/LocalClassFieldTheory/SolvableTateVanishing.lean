/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientKernel
public import FLT.LocalClassFieldTheory.SolvableTateSplice

/-!
# The finite-solvable adjacent-vanishing criterion

The norm-splice induction and the two constructed coefficient sequences
propagate adjacent subgroup vanishing to every integer Tate degree.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G]

/-- Forward dimension shifting transports subgroup vanishing. -/
theorem SubgroupTateVanishing.shift {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing M (n + 1)) :
    SubgroupTateVanishing (shiftedCoefficients M) n := by
  intro H _
  exact (h H).of_iso (coinducedSubgroupShift M H n)

/-- Forward dimension shifting reflects subgroup vanishing. -/
theorem SubgroupTateVanishing.unshift {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing (shiftedCoefficients M) n) :
    SubgroupTateVanishing M (n + 1) := by
  intro H _
  exact (h H).of_iso (coinducedSubgroupShift M H n).symm

variable [Fintype G]

/-- Reverse dimension shifting transports subgroup vanishing. -/
theorem SubgroupTateVanishing.kernel {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing M n) :
    SubgroupTateVanishing (kernelCoefficients M) (n + 1) := by
  intro H _
  exact (h H).of_iso (coinducedKernelSubgroupShift M H n).symm

/-- Reverse dimension shifting reflects subgroup vanishing. -/
theorem SubgroupTateVanishing.unkernel {M : Rep k G} {n : ℤ}
    (h : SubgroupTateVanishing (kernelCoefficients M) (n + 1)) :
    SubgroupTateVanishing M n := by
  intro H _
  exact (h H).of_iso (coinducedKernelSubgroupShift M H n)

variable [Group.IsSolvable G]

omit [Fintype G] in
/-- Adjacent vanishing propagates to every nonnegative degree on every subgroup. -/
theorem solvable_subgroup_tate_nat_isZero (n : ℕ) (M : Rep k G)
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) :
    SubgroupTateVanishing M n := by
  induction n generalizing M with
  | zero => exact h₀
  | succ n ih =>
    have hm : SubgroupTateVanishing (shiftedCoefficients M) (-1) := h₀.shift
    have hz : SubgroupTateVanishing (shiftedCoefficients M) 0 := h₁.shift
    have ho : SubgroupTateVanishing (shiftedCoefficients M) 1 := by
      intro H _
      exact solvable_tate_one_isZero _ (hm.res H) (hz.res H)
    simpa only [Nat.cast_add, Nat.cast_one] using (ih _ hz ho).unshift

omit [Fintype G] in
/-- Adjacent vanishing propagates to every negative degree on every subgroup. -/
theorem solvable_subgroup_tate_neg_isZero [Finite G] (n : ℕ) (M : Rep k G)
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) :
    SubgroupTateVanishing M (-(n : ℤ) - 1) := by
  let : Fintype G := Fintype.ofFinite G
  induction n generalizing M with
  | zero =>
    intro H _
    exact solvable_tate_neg_one_isZero _ (h₀.res H) (h₁.res H)
  | succ n ih =>
    have hm : SubgroupTateVanishing M (-1) := by
      intro H _
      exact solvable_tate_neg_one_isZero _ (h₀.res H) (h₁.res H)
    have hz : SubgroupTateVanishing (kernelCoefficients M) 0 := hm.kernel
    have ho : SubgroupTateVanishing (kernelCoefficients M) 1 := h₀.kernel
    have hs := ih (kernelCoefficients M) hz ho
    have he : -(n : ℤ) - 1 = (-(↑(n + 1) : ℤ) - 1) + 1 := by omega
    rw [he] at hs
    exact hs.unkernel

/-- All-degree Tate vanishing for finite solvable groups from adjacent subgroup vanishing. -/
theorem solvable_tate_isZero_of_adjacent (M : Rep k G)
    (h₀ : SubgroupTateVanishing M 0) (h₁ : SubgroupTateVanishing M 1) (n : ℤ) :
    Limits.IsZero (tateCohomology M n) := by
  cases n with
  | ofNat n => exact (solvable_subgroup_tate_nat_isZero n M h₀ h₁).self
  | negSucc n =>
    simpa only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one, neg_add, sub_eq_add_neg] using
      (solvable_subgroup_tate_neg_isZero n M h₀ h₁).self

end LocalClassFieldTheory
