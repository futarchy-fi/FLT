/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicQuotient
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp

/-!
# Exact sequences of ideal-adic quotients

The adjacent graded coefficient I^n M / I^(n+1) M is the kernel of
M / I^(n+1) M → M / I^n M. This is the actual cokernel-composition
sequence, transported along the proved power-inclusion identity.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.GlobalIdealPower FLT.Mazur.GlobalIdealPowerCompatibility
open FLT.Mazur.FCurve.CoherentDevissage

universe u

namespace FLT.Mazur.IdealAdicQuotient

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- The n-th associated-graded coefficient of the actual ideal filtration. -/
def graded (n : ℕ) : X.Modules := cokernel (powerStep I M n)

instance graded_coherent (n : ℕ) : (graded I M n).IsFinitePresentation :=
  coherent_cokernel (powerStep I M n)

/-- Each associated-graded coefficient is killed by the ideal. -/
theorem graded_idealKilled (n : ℕ) : IdealKilled I (graded I M n) :=
  idealKilled_powerStep_cokernel I M n

/-- The natural map from the graded coefficient into the next quotient. -/
def gradedInclusion (n : ℕ) : graded I M n ⟶ quotient I M (n + 1) :=
  cokernel.desc (powerStep I M n) (inclusion (I ^ n) M ≫ projection I M (n + 1)) (by
    rw [← Category.assoc, transition_comp]
    exact cokernel.condition _)

/-- The inclusion is compatible with the original power coefficient. -/
@[reassoc (attr := simp)]
lemma gradedProjection_inclusion (n : ℕ) :
    cokernel.π (powerStep I M n) ≫ gradedInclusion I M n =
      inclusion (I ^ n) M ≫ projection I M (n + 1) :=
  cokernel.π_desc _ _ _

/-- The graded coefficient maps to zero on the preceding quotient. -/
@[reassoc (attr := simp)]
lemma gradedInclusion_reduction (n : ℕ) :
    gradedInclusion I M n ≫ reduction I M (Nat.le_succ n) = 0 := by
  apply (cancel_epi (cokernel.π (powerStep I M n))).mp
  rw [← Category.assoc, gradedProjection_inclusion, Category.assoc, projection_reduction]
  exact cokernel.condition _

/-- The actual adjacent graded short complex. -/
def gradedSequence (n : ℕ) : ShortComplex X.Modules :=
  ShortComplex.mk (gradedInclusion I M n) (reduction I M (Nat.le_succ n))
    (gradedInclusion_reduction I M n)

private theorem cokernelComp_shortExact {C : Type*} [Category* C] [Abelian C]
    {A B D : C} (a : A ⟶ B) (b : B ⟶ D) [Mono b] (c : A ⟶ D) (w : a ≫ b = c) :
    (ShortComplex.mk
      (cokernel.desc a (b ≫ cokernel.π c) (by rw [← Category.assoc, w]; simp))
      (cokernel.desc c (cokernel.π b) (by rw [← w, Category.assoc]; simp))
      (by apply (cancel_epi (cokernel.π a)).mp; simp)).ShortExact := by
  subst c
  have h := kernelCokernelCompSequence_exact a b
  let : Mono (kernelCokernelCompSequence.snakeInput a b).L₃.f :=
    (h.exact 2).mono_g ((isZero_kernel_of_mono b).eq_of_src _ _)
  let : Epi (kernelCokernelCompSequence.snakeInput a b).L₃.g := by
    dsimp [kernelCokernelCompSequence.snakeInput, cokernel.map]
    infer_instance
  have hs : (kernelCokernelCompSequence.snakeInput a b).L₃.ShortExact :=
    ⟨(kernelCokernelCompSequence.snakeInput a b).L₃_exact⟩
  simpa only [kernelCokernelCompSequence.snakeInput, cokernel.map, Category.id_comp] using hs

/-- Consecutive ideal quotients form the canonical short exact sequence. -/
theorem gradedSequence_shortExact (n : ℕ) : (gradedSequence I M n).ShortExact :=
  cokernelComp_shortExact (powerStep I M n) (inclusion (I ^ n) M)
    (inclusion (I ^ (n + 1)) M) (transition_comp I M (Nat.le_succ n))

end FLT.Mazur.IdealAdicQuotient
