/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.PadicCyclotomicRelativeDegree

/-! # The relative cyclotomic minimal polynomial -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
open Polynomial
variable (p : ℕ) [hp : Fact p.Prime]

/-- Raising an upper-level root to the relative degree puts it in the lower field. -/
theorem padicCyclotomic_pow_mem (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : ζ ^ (p ^ (n + r + 1)) = 1) :
    ζ ^ (p ^ r) ∈ padicCyclotomicTower p (n + 1) := by
  apply padicCyclotomicTower_root_mem
  rw [← pow_mul, ← pow_add, show r + (n + 1) = n + r + 1 by omega]
  exact hζ

/-- A primitive upper root has binomial minimal polynomial over a positive lower level. -/
theorem padicCyclotomicRelative_minpoly (n r : ℕ) (ζ : PadicAlgCl p)
    (hζ : IsPrimitiveRoot ζ (p ^ (n + r + 1))) :
    minpoly (padicCyclotomicTower p (n + 1)) ζ =
      X ^ (p ^ r) - C ⟨ζ ^ (p ^ r), padicCyclotomic_pow_mem p n r ζ hζ.pow_eq_one⟩ := by
  have hi : IsIntegral (padicCyclotomicTower p (n + 1)) ζ :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[p]) ζ).tower_top
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi)
    (monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero))
  · apply minpoly.dvd
    simp only [map_sub, map_pow, aeval_X, aeval_C, IntermediateField.algebraMap_apply, sub_self]
  · rw [natDegree_X_pow_sub_C, padicCyclotomicRelative_minpoly_natDegree p n r ζ hζ]

end PadicHodgeTheory
