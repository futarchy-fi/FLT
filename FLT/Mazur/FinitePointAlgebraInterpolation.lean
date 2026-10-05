/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.Choose

/-!
# Interpolation in the algebra of a finite set of points

An algebra map to functions on a finite set is surjective as soon as its image
separates points. Products of normalized separating functions construct the
individual characteristic functions, over an arbitrary field.
-/

@[expose] public section

namespace FLT.Mazur

open scoped BigOperators

variable {K B ι : Type*} [Field K] [CommRing B] [Algebra K B] [Finite ι]

/-- A separating algebra map onto a finite point algebra is surjective. -/
theorem finitePointAlgebra_surjective (f : B →ₐ[K] (ι → K))
    (h : ∀ i j : ι, i ≠ j → ∃ b : B, f b i ≠ f b j) : Function.Surjective f := by
  classical
  let _ := Fintype.ofFinite ι
  have pair (i j : ι) (hij : i ≠ j) : ∃ b : B, f b i = 1 ∧ f b j = 0 := by
    obtain ⟨b, hb⟩ := h i j hij
    refine ⟨algebraMap K B (f b i - f b j)⁻¹ * (b - algebraMap K B (f b j)), ?_, ?_⟩
    · simp only [map_mul, map_sub, AlgHom.commutes, Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      exact inv_mul_cancel₀ (sub_ne_zero.mpr hb)
    · simp only [map_mul, map_sub, AlgHom.commutes, Pi.mul_apply, Pi.sub_apply,
        Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, sub_self, mul_zero]
  have delta (i : ι) : ∃ b : B, ∀ j, f b j = if i = j then 1 else 0 := by
    choose b hb using pair i
    let c (j : ι) : B := if hij : i = j then 1 else b j hij
    have hc (j : ι) (hij : i ≠ j) : f (c j) i = 1 ∧ f (c j) j = 0 := by
      simpa only [c, dite_eq_right hij] using hb j hij
    refine ⟨∏ j ∈ Finset.univ.erase i, c j, ?_⟩
    intro j
    rw [map_prod, Finset.prod_apply]
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro k hk
      exact (hc k (Ne.symm (Finset.mem_erase.mp hk).1)).1
    · rw [ite_eq_right hij]
      exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j⟩)
        (hc j hij).2
  choose b hb using delta
  intro v
  refine ⟨∑ i, algebraMap K B (v i) * b i, ?_⟩
  ext j
  simp only [map_sum, Finset.sum_apply, map_mul, Pi.mul_apply, AlgHom.commutes,
    Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hb]
  simp

end FLT.Mazur
