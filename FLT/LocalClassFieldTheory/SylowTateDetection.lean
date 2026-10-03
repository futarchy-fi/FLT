/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.CoinducedCoefficientKernel
public import FLT.LocalClassFieldTheory.CoinducedTateShift
public import FLT.LocalClassFieldTheory.SylowNormDetection

/-!
# All-degree Tate detection on Sylow subgroups

Both dimension shifts preserve Sylow acyclicity. Iterating them reduces
arbitrary integer degrees to the proved degree-zero norm detection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] [Fintype G]

omit [Fintype G] in
/-- Acyclicity on Sylow subgroups survives the forward coefficient shift. -/
theorem sylowTateVanishing_shift (M : Rep k G) (h : ∀ n, SylowTateVanishing M n)
    (n : ℤ) : SylowTateVanishing (shiftedCoefficients M) n := by
  intro p _ P _
  exact (h (n + 1) p P).of_iso (coinducedSubgroupShift M P n)

/-- Acyclicity on Sylow subgroups survives the reverse coefficient shift. -/
theorem sylowTateVanishing_kernel (M : Rep k G) (h : ∀ n, SylowTateVanishing M n)
    (n : ℤ) : SylowTateVanishing (kernelCoefficients M) n := by
  intro p _ P _
  have hz := (h (n - 1) p P).of_iso (coinducedKernelSubgroupShift M P (n - 1)).symm
  simpa only [sub_add_cancel] using hz

/-- Sylow acyclicity kills every nonnegative Tate degree. -/
theorem tate_nat_isZero_of_sylow (n : ℕ) (M : Rep k G)
    (h : ∀ i, SylowTateVanishing M i) : Limits.IsZero (tateCohomology M n) := by
  induction n generalizing M with
  | zero => exact tate_zero_isZero_of_sylow M (h 0)
  | succ n ih =>
    have hz := (ih (shiftedCoefficients M) (sylowTateVanishing_shift M h)).of_iso
      (coinducedTateShift M n).symm
    simpa only [Nat.cast_add, Nat.cast_one] using hz

/-- Sylow acyclicity kills every nonpositive Tate degree. -/
theorem tate_neg_nat_isZero_of_sylow (n : ℕ) (M : Rep k G)
    (h : ∀ i, SylowTateVanishing M i) : Limits.IsZero (tateCohomology M (-(n : ℤ))) := by
  induction n generalizing M with
  | zero => exact tate_zero_isZero_of_sylow M (h 0)
  | succ n ih =>
    have hz := ih (kernelCoefficients M) (sylowTateVanishing_kernel M h)
    have he : -(n : ℤ) = -(↑(n + 1) : ℤ) + 1 := by omega
    rw [he] at hz
    exact hz.of_iso (coinducedKernelShift M (-(↑(n + 1) : ℤ)))

/-- Vanishing of all Sylow Tate groups implies vanishing in every integer degree. -/
theorem tate_isZero_of_sylow (M : Rep k G) (h : ∀ i, SylowTateVanishing M i) (n : ℤ) :
    Limits.IsZero (tateCohomology M n) := by
  cases n with
  | ofNat n => exact tate_nat_isZero_of_sylow n M h
  | negSucc n => exact tate_neg_nat_isZero_of_sylow (n + 1) M h

end LocalClassFieldTheory
