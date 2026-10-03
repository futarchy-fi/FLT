/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexCyclotomicLog
public import FLT.PadicHodgeTheory.ComplexCyclotomicPrincipal
public import FLT.PadicHodgeTheory.ComplexDeRhamDVR

/-! # The completed cyclotomic difference is a uniformizer -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The canonical map from A_inf to its localized theta-adic completion. -/
def complexAinfToDeRham : Ainf p →+* ComplexBDeRhamPlus p :=
  (algebraMap (ComplexAinfInvertP p) (ComplexBDeRhamPlus p)).comp
    (algebraMap (Ainf p) (ComplexAinfInvertP p))

/-- The integral cyclotomic generator also generates the localized theta kernel. -/
theorem complexCyclotomicKernel_localized_span :
    RingHom.ker (complexThetaInvertP p) =
      Ideal.span {algebraMap (Ainf p) (ComplexAinfInvertP p) (complexCyclotomicKernel p)} := by
  rw [complexThetaInvertP_ker_eq_span]
  exact Ideal.span_singleton_eq_span_singleton.mpr
    ((complexCyclotomicKernel_associated p).map _)

/-- The completed geometric sum is associated to the existing parameter. -/
theorem complexCyclotomicKernel_completed_associated :
    Associated (complexDeRhamParameter p)
      (complexAinfToDeRham p (complexCyclotomicKernel p)) :=
  (complexCyclotomicKernel_associated p).map (complexAinfToDeRham p)

/-- The shifted factor is a unit in B_dR^+, since its theta image is nonzero. -/
theorem complexCyclotomicShiftDifference_completed_isUnit :
    IsUnit (complexAinfToDeRham p (complexCyclotomicShiftDifference p)) := by
  by_contra h
  have hm : complexAinfToDeRham p (complexCyclotomicShiftDifference p) ∈
      IsLocalRing.maximalIdeal (ComplexBDeRhamPlus p) := h
  rw [complexDeRham_maximalIdeal, ← complexDeRhamTheta_ker] at hm
  change complexDeRhamTheta p
    (complexAinfToDeRham p (complexCyclotomicShiftDifference p)) = 0 at hm
  rw [complexAinfToDeRham, RingHom.comp_apply, complexDeRhamTheta_algebraMap,
    complexCyclotomicShiftDifference_theta] at hm
  have he : complexCyclotomicRoot p - 1 = 0 := Subtype.val_injective hm
  exact (complexCyclotomicRoot_primitive p).ne_one (Fact.out : p.Prime).one_lt
    (sub_eq_zero.mp he)

/-- The integral factorization survives localization and completion. -/
theorem complexCyclotomicArgument_factor :
    complexCyclotomicArgument p = complexAinfToDeRham p (complexCyclotomicKernel p) *
      complexAinfToDeRham p (complexCyclotomicShiftDifference p) := by
  change complexAinfToDeRham p (complexCyclotomicDifference p) = _
  rw [complexCyclotomicDifference_factor, map_mul]

/-- The actual completed cyclotomic difference is associated to the parameter. -/
theorem complexCyclotomicArgument_associated :
    Associated (complexDeRhamParameter p) (complexCyclotomicArgument p) := by
  rw [complexCyclotomicArgument_factor]
  exact (complexCyclotomicKernel_completed_associated p).trans
    (associated_mul_unit_right _ _ (complexCyclotomicShiftDifference_completed_isUnit p))

/-- The cyclotomic difference generates the actual maximal ideal. -/
theorem complexCyclotomicArgument_span :
    Ideal.span {complexCyclotomicArgument p} =
      IsLocalRing.maximalIdeal (ComplexBDeRhamPlus p) := by
  rw [complexDeRham_maximalIdeal]
  exact Ideal.span_singleton_eq_span_singleton.mpr (complexCyclotomicArgument_associated p).symm

/-- The cyclotomic difference is a nonzero uniformizer in the completed ring. -/
theorem complexCyclotomicArgument_irreducible : Irreducible (complexCyclotomicArgument p) :=
  (complexCyclotomicArgument_associated p).irreducible (complexDeRhamParameter_irreducible p)

/-- Completion does not kill the cyclotomic difference. -/
theorem complexCyclotomicArgument_ne_zero : complexCyclotomicArgument p ≠ 0 :=
  (complexCyclotomicArgument_irreducible p).ne_zero

end PadicHodgeTheory
