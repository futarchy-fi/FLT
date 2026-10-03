/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicShift

/-! # The cyclotomic geometric sum in the actual Fontaine kernel -/

@[expose] public noncomputable section
open Finset
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The geometric sum at the Teichmuller lift of shifted epsilon. -/
def complexCyclotomicKernel : Ainf p :=
  ∑ i ∈ range p, WittVector.teichmuller p (complexCyclotomicShift p 1) ^ i

/-- The second factor in the cyclotomic difference. -/
def complexCyclotomicShiftDifference : Ainf p :=
  WittVector.teichmuller p (complexCyclotomicShift p 1) - 1

/-- The geometric sum vanishes under the actual theta map. -/
theorem complexCyclotomicKernel_mem_ker :
    complexCyclotomicKernel p ∈ RingHom.ker (complexTheta p) := by
  change complexTheta p (complexCyclotomicKernel p) = 0
  simp only [complexCyclotomicKernel, map_sum, map_pow, complexTheta_teichmuller,
    complexCyclotomicShift_one_sharp]
  exact (complexCyclotomicRoot_primitive p).geom_sum_eq_zero (Fact.out : p.Prime).one_lt

/-- The shifted factor has nonzero theta image. -/
theorem complexCyclotomicShiftDifference_theta :
    complexTheta p (complexCyclotomicShiftDifference p) = complexCyclotomicRoot p - 1 := by
  rw [complexCyclotomicShiftDifference, map_sub, map_one, complexTheta_teichmuller,
    complexCyclotomicShift_one_sharp]

/-- The cyclotomic difference factors in A_inf itself. -/
theorem complexCyclotomicDifference_factor :
    complexCyclotomicDifference p =
      complexCyclotomicKernel p * complexCyclotomicShiftDifference p := by
  rw [complexCyclotomicKernel, complexCyclotomicShiftDifference, geom_sum_mul,
    ← map_pow, complexCyclotomicShift_pow, complexCyclotomicShift_zero]
  rfl

/-- The geometric sum is nonzero before any localization. -/
theorem complexCyclotomicKernel_ne_zero : complexCyclotomicKernel p ≠ 0 := by
  intro h
  exact complexCyclotomicDifference_ne_zero p (by
    rw [complexCyclotomicDifference_factor, h, zero_mul])

/-- Its zeroth Witt coefficient is the geometric sum in the actual tilt. -/
theorem complexCyclotomicKernel_coeff_zero :
    (complexCyclotomicKernel p).coeff 0 =
      ∑ i ∈ range p, complexCyclotomicShift p 1 ^ i := by
  change WittVector.constantCoeff (complexCyclotomicKernel p) = _
  simp only [complexCyclotomicKernel, map_sum, map_pow]
  rfl

end PadicHodgeTheory
