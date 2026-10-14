/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

/-!
# Finite comparison across a retained Cartier parameter

A finite algebra map is invertible near a Cartier divisor if its divisor
quotient is invertible and the parameter remains regular upstairs.
Nakayama is applied separately to the cokernel and to the original kernel;
no flatness of the entire algebra map is required.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteCartierComparison

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
local notation "f" => algebraMap R A

/-- Lifting every element modulo a Jacobson parameter makes a finite algebra map onto. -/
theorem surjective_of_mod_parameter [Module.Finite R A] (t : R)
    (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hs : ∀ b : A, ∃ a : R, b - f a ∈ Ideal.span {f t}) :
    Function.Surjective (f) := by
  change Function.Surjective (Algebra.linearMap R A)
  apply LinearMap.range_eq_top.mp
  apply top_unique
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {t}) Module.Finite.fg_top
    (by simpa only [Ideal.span_singleton_le_iff_mem] using ht)
  intro b _
  obtain ⟨a, ha⟩ := hs b
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
  have hb : b = f a + t • c := by
    rw [Algebra.smul_def, ← hc]
    abel
  rw [hb]
  exact Submodule.add_mem_sup ⟨a, rfl⟩
    (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) (Submodule.mem_top))

/-- A regular pulled parameter and quotient injectivity kill the original finite kernel. -/
theorem injective_of_mod_parameter [IsNoetherianRing R] (t : R)
    (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (hi : ∀ a : R, f a ∈ Ideal.span {f t} → a ∈ Ideal.span {t}) :
    Function.Injective (f) := by
  apply (RingHom.injective_iff_ker_eq_bot (f)).mpr
  apply le_antisymm _ bot_le
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := Ideal.span {t})
    (IsNoetherian.noetherian (RingHom.ker (f)))
    (by simpa only [Ideal.span_singleton_le_iff_mem] using ht)
  rw [bot_sup_eq]
  intro a ha
  have hfa : f a = 0 := ha
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hi a (by rw [hfa]; exact Ideal.zero_mem _))
  have hfb : f b = 0 := by
    apply (mem_nonZeroDivisors_iff_left.mp hreg)
    rw [← map_mul, ← hb, hfa]
  rw [hb]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) hfb

/-- A bijective Cartier quotient and a retained regular parameter determine the finite map. -/
theorem bijective_of_mod_parameter [IsNoetherianRing R] [Module.Finite R A] (t : R)
    (ht : t ∈ Ideal.jacobson (⊥ : Ideal R))
    (hreg : f t ∈ nonZeroDivisors A)
    (hs : ∀ b : A, ∃ a : R, b - f a ∈ Ideal.span {f t})
    (hi : ∀ a : R, f a ∈ Ideal.span {f t} → a ∈ Ideal.span {t}) :
    Function.Bijective (f) :=
  ⟨injective_of_mod_parameter t ht hreg hi, surjective_of_mod_parameter t ht hs⟩

end FLT.Mazur.FiniteCartierComparison
