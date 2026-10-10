/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SplitEvaluationTensorKernel
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# The open injectivity locus of a finite split evaluation

For a split linear evaluation on a finite module, injectivity after tensoring
with a residue field is the complement of the support of its kernel. The
kernel is finite even over a non-Noetherian base, so this locus is open.
Relating these tensor fibers to geometric fiber functions is a separate step.
-/

@[expose] public noncomputable section

open TensorProduct

namespace FLT.Mazur.Approximation

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module.Finite R M]
  (ε : M →ₗ[R] N) (σ : N →ₗ[R] M) (h : ε.comp σ = LinearMap.id)

include h in
/-- The injective residue evaluations are exactly the complement of the kernel support. -/
theorem residueEvaluationLocus_eq_compl_support :
    {p : PrimeSpectrum R | Function.Injective (ε.lTensor p.asIdeal.ResidueField)} =
      (Module.support R ε.ker)ᶜ := by
  have := finite_splitEvaluationKernel ε σ h
  ext p
  rw [Set.mem_ofPred_eq, splitEvaluation_lTensor_injective_iff ε σ h,
    Set.mem_compl_iff, Module.mem_support_iff_nontrivial_residueField_tensorProduct,
    not_nontrivial_iff_subsingleton]

include h in
/-- Injectivity of residue-field evaluations is an open condition for a finite split module. -/
theorem isOpen_residueEvaluationLocus :
    IsOpen {p : PrimeSpectrum R | Function.Injective (ε.lTensor p.asIdeal.ResidueField)} := by
  have := finite_splitEvaluationKernel ε σ h
  rw [residueEvaluationLocus_eq_compl_support ε σ h]
  exact (Module.isClosed_support (R := R) (M := ε.ker)).isOpen_compl

/-- A finite algebra augmentation has an open injective residue-evaluation locus. -/
theorem isOpen_residueAugmentationLocus {B : Type*} [CommRing B] [Algebra R B]
    [Module.Finite R B] (e : B →ₐ[R] R) :
    IsOpen {p : PrimeSpectrum R |
      Function.Injective (e.toLinearMap.lTensor p.asIdeal.ResidueField)} := by
  apply isOpen_residueEvaluationLocus e.toLinearMap (Algebra.linearMap R B)
  apply LinearMap.ext
  intro r
  exact e.commutes r

end FLT.Mazur.Approximation
