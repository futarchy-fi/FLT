/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FreeTargetVanishingIdeal
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finite equations for vanishing in a free target

A finite set of source generators contributes only finitely many nonzero
coordinates, even when the target basis is infinite. These coordinates
generate the full coefficient ideal, with no Noetherian hypothesis.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FreeTargetVanishing
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] (b : Module.Basis ι R N) (f : M →ₗ[R] N)

/-- The finite nonzero coefficients of a chosen finite family of source vectors. -/
def generatorCoefficients (s : Finset M) : Finset R := by
  classical
  exact s.biUnion fun x => (b.repr (f x)).support.image (b.repr (f x))

/-- Every coordinate of a chosen source vector lies in the finite coefficient span. -/
theorem generator_coordinate_mem (s : Finset M) {x : M} (hx : x ∈ s) (i : ι) :
    b.repr (f x) i ∈ Ideal.span (generatorCoefficients b f s : Set R) := by
  classical
  by_cases hi : i ∈ (b.repr (f x)).support
  · apply Ideal.subset_span
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact Ideal.zero_mem _

/-- Source generators give exactly the original coefficient ideal, without taking radicals. -/
theorem ideal_eq_generator_span (s : Finset M)
    (hs : Submodule.span R (s : Set M) = ⊤) :
    ideal b f = Ideal.span (generatorCoefficients b f s : Set R) := by
  classical
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨⟨x, i⟩, rfl⟩
    have hx : x ∈ Submodule.span R (s : Set M) := by rw [hs]; trivial
    have h : ∀ i, b.repr (f x) i ∈
        Ideal.span (generatorCoefficients b f s : Set R) := by
      induction hx using Submodule.span_induction with
      | mem x hx => exact generator_coordinate_mem b f s hx
      | zero => intro i; simp
      | add x y _ _ hx hy =>
        intro i
        simpa using Ideal.add_mem _ (hx i) (hy i)
      | smul r x _ hx =>
        intro i
        simpa using Ideal.mul_mem_left _ r (hx i)
    exact h i
  · apply Ideal.span_le.mpr
    intro r hr
    obtain ⟨x, _, hx⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Ideal.subset_span ⟨(x, i), rfl⟩

/-- Finite generation of the source gives finite generation of the full coefficient ideal. -/
theorem ideal_fg [Module.Finite R M] : (ideal b f).FG := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := M)
  exact ⟨generatorCoefficients b f s, (ideal_eq_generator_span b f s hs).symm⟩

end FLT.Mazur.FreeTargetVanishing
